/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate


@[expose] public section
set_option autoImplicit false

/-!
# Rust ↔ dialect-front simulation over the `CProg`-free front

This file proves the `LowCT`-source relational simulation **directly over the
`CProg`-free dialect front** `translateDialectControl` / `DTransOut`, by a
induction on the `RustExec` derivation. For a control-covered `LowCT` whose
direct dialect translation succeeds with output `o`, every concrete `RustExec`
trace lands a post-state valuation satisfying `RustStateInterp` *at the dialect
front's* `o.Γ'` / `o.vm`. Neither the statement nor the proof names `CProg`,
`CExpr`, `TransOut`, or `translate`.

## Proof structure

The induction mirrors the structure of the byte-layout simulation: per
`RustExec` step it constructs a `RustStateInterp` witness. `RustStateInterp`,
`bindingOK`, and the per-constructor transport lemmas (`interp_bind_*`,
`interp_cons_*`, `noAlias_*`, `bindingOK_*`) live over the shared
`VarMap`/`RustState` substrate, so they carry to the dialect unchanged; the
proof differs from the `CProg` development only in unfolding the dialect front
(`translateDialectControl` / `translateDialectFull` / `translateDialect`) in
place of `translate`, and in the `RCallN` fold (`loopCallNDestsD_interp_extend`),
which walks the rust state along `callNUpdate` one destination at a time.

The coverage hypothesis `hCov : IsCoveredCtl c` is reverted into the induction:
because the dialect front is *partial*, every `RustExec` constructor outside
`IsCoveredCtl` (e.g. `RLetZero`, `RAssert`, …) is discharged by
inversion of `hCov` (`cases hCov`), and the recursive arms
thread sub-coverage to their IHs.

The `RIfNz` arms (`ifTrue` / `ifFalse`) and the `RWhileNz` arms (`whileFalse` /
`whileTrue`) close via `noAlias_canonical_witness`: the post-branch / post-loop
state's witness at `o.vm` is realised from `NoAliasVM o.vm`, which holds because
the dialect front preserves `NoAliasVM`
(`translateDialectControl_preserves_noAlias`).

## Fragment used

`IsCoveredCtl` — the leaf-call covered arms plus `RFor` (bounded unroll),
`RIfNz` (φ-merge) and `RWhileNz` (data-dependent loop, context-invariant front
output). Not-yet-in-dialect ops are excluded.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustVal LeafSpec RustExec Located TowerType
  locatedUpdate locatedLookup rsSetScalar rsSetTower rsSetTower_same
  callNLeafName callNUpdate)

/-- **`loopCallNDestsD` interp-extension fold (dialect twin).**
    From a witness `(V, hInv)` for `(vm, rs)` and
    `loopCallNDestsD f args vm dests i = some o`, build a witness `V'` for
    `(o.vm, callNUpdate leafSpec f argTs argList i dests rs)`.

    `RustExec.callN` writes each destination in turn, so the rust state moves
    along the fold: destination `i` is `rsSetTower` to the output of
    `leafSpec.call (callNLeafName f i)`, matched on the dialect side by one
    fresh binding through `interp_cons_setTower_any`. That lemma is
    `∃`-quantified over the dialect-side value, so the witness it produces
    records the shape of the extension, not agreement between the dialect value
    and the oracle output. -/
theorem loopCallNDestsD_interp_extend (leafSpec : LeafSpec) (fname : String)
    (args : List Located) (argTs : List TowerType)
    (argList : List (Σ t : TowerType, RustVal t)) :
    ∀ {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
      (_hInv : RustStateInterp vm rs V) (dests : List Located) (i : Nat)
      {o : DTransOut Γ},
      loopCallNDestsD fname args vm dests i = some o →
        ∃ V' : HVec o.Γ',
          RustStateInterp o.vm (callNUpdate leafSpec fname argTs argList i dests rs) V'
  | _, vm, rs, V, hInv, [], i, o, hL => by
      simp only [loopCallNDestsD, Option.some.injEq] at hL
      subst hL; exact ⟨V, hInv⟩
  | _, vm, rs, V, hInv, d :: rest, i, o, hL => by
      simp only [loopCallNDestsD] at hL
      split at hL
      · exact absurd hL (by simp)
      · rename_i resolvedArgs heqRes
        obtain ⟨argTys, hv⟩ := listSigmaToCHVector resolvedArgs
        split at hL
        · exact absurd hL (by simp)
        · rename_i oRest hRest
          simp only [Option.some.injEq] at hL
          subst hL
          simp only [callNUpdate, locatedUpdate]
          obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv d.locVar (encodeTy d.locDst)
            ⟨d.locDst, leafSpec.call (callNLeafName fname i) d.locDst argTs
              ((locatedLookup rs d).getD default) argList⟩
          exact loopCallNDestsD_interp_extend leafSpec fname args argTs argList
            hInv' rest (i + 1) hRest

/-! ## `NoAliasVM` preservation by the `CProg`-free front

The `RIfNz` arms of the simulation produce a witness at the post-branch state
via `noAlias_canonical_witness` — the byte-correspondence valuation
`HVec.ofVarFn (witVarFn o.vm rs)` (the same lever the `whileTrue` arm uses),
which is satisfiable at *any* state given `NoAliasVM o.vm`. So we only need that
the dialect front preserves `NoAliasVM`, proved below by structural recursion
over `IsCoveredCtl` (no `CProg`, no `translate`). -/

/-- `loopCallNDestsD` preserves `NoAliasVM`: each destination binds one fresh
    name (`noAlias_bind`), at any starting output index. -/
theorem loopCallNDestsD_preserves_noAlias (fname : String) (args : List Located) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (dests : List Located) {i : Nat} {o : DTransOut Γ},
      loopCallNDestsD fname args vm dests i = some o → NoAliasVM vm → NoAliasVM o.vm
  | _, vm, [], i, o, hL, hNA => by
      simp only [loopCallNDestsD, Option.some.injEq] at hL
      subst hL; exact hNA
  | _, vm, d :: rest, i, o, hL, hNA => by
      simp only [loopCallNDestsD] at hL
      split at hL
      · exact absurd hL (by simp)
      · rename_i ra hra
        obtain ⟨argTys, hv⟩ := listSigmaToCHVector ra
        split at hL
        · exact absurd hL (by simp)
        · rename_i oRest hRest
          simp only [Option.some.injEq] at hL
          subst hL
          exact loopCallNDestsD_preserves_noAlias fname args (vm.bind d.locVar) rest hRest
            (noAlias_bind hNA d.locVar)

/-- `loopRForD` preserves `NoAliasVM`, given per-iteration body preservation:
    each iteration binds the counter (`noAlias_bind`) then threads the body. -/
theorem loopRForD_preserves_noAlias {Γ : Ctx}
    (translateBodyD : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (x : String)
    (hbody : ∀ {Γ'' : Ctx} (vm'' : VarMap Γ'') {o : DTransOut Γ''},
      translateBodyD vm'' = some o → NoAliasVM vm'' → NoAliasVM o.vm)
    (vm : VarMap Γ) :
    ∀ (N : Nat) {o : DTransOut Γ},
      loopRForD translateBodyD vm x N = some o → NoAliasVM vm → NoAliasVM o.vm
  | 0, o, hL, hNA => by
      simp only [loopRForD, Option.some.injEq] at hL; subst hL; exact hNA
  | n + 1, o, hL, hNA => by
      simp only [loopRForD] at hL
      cases hPre : loopRForD translateBodyD vm x n with
      | none => rw [hPre] at hL; exact absurd hL (by simp)
      | some oPre =>
          rw [hPre] at hL; simp only at hL
          cases hB : translateBodyD (oPre.vm.bind x) with
          | none => rw [hB] at hL; exact absurd hL (by simp)
          | some oBody =>
              rw [hB] at hL; simp only [Option.some.injEq] at hL; subst hL
              have hPreNA := loopRForD_preserves_noAlias translateBodyD x hbody vm n hPre hNA
              exact hbody (oPre.vm.bind x) hB (noAlias_bind hPreNA x)

/-- The scalar-`SExpr` chain preserves `NoAliasVM`: every node is a fresh `bind`
    (`pushVarBind`) over the threaded `seqOut` context, so `NoAliasVM` is kept by
    `noAlias_bind`. By induction on the `SExpr`. -/
theorem lowerSExpr_preserves_noAlias {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat)
    (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) {o : DTransOut Γ} {nm : String} {cnt' : Nat}
    (h : lowerSExpr vm cnt e = some (o, nm, cnt')) (hNA : NoAliasVM vm) : NoAliasVM o.vm := by
  induction e generalizing Γ vm cnt o nm cnt' with
  | SVar x =>
      simp only [lowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ho, _⟩ := h; subst ho; exact hNA
      · exact absurd h (by simp)
  | SLit n =>
      simp only [lowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, _⟩ := h; subst ho
      exact noAlias_bind hNA _
  | SAdd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SSub a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SMul a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SAnd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SXor a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SShl a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SShr a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SLt _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SAsr _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulHiU a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   exact noAlias_bind (ihb oa.vm cnt1 heqB (iha vm cnt heqA hNA)) _)
                | exact absurd h (by simp)
  | SMulHiS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SLimb _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)

/-- The multi-binding (`IsCovered`) front preserves `NoAliasVM`: every arm grows
    `vm` by `bind`/`weaken` steps (and the `RCallN` fold), each `NoAliasVM`-safe. -/
theorem translateDialectFull_preserves_noAlias {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCovered c) {o : DTransOut Γ}
    (hT : translateDialectFull vm c = some o) (hNA : NoAliasVM vm) : NoAliasVM o.vm := by
  induction hc generalizing Γ vm o with
  | rAssert _label =>
      simp only [translateDialectFull, Option.some.injEq] at hT
      subst hT
      exact hNA
  | rSkip =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at hT
      subst hT; exact hNA
  | rScalarSet name n =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at hT
      subst hT; exact noAlias_bind hNA name
  | @rSeq c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      simp only [translateDialectFull] at hT
      cases hd1 : translateDialectFull vm c₁ with
      | none => rw [hd1] at hT; exact absurd hT (by simp)
      | some o₁ =>
        rw [hd1] at hT; simp only at hT
        cases hd2 : translateDialectFull o₁.vm c₂ with
        | none => rw [hd2] at hT; exact absurd hT (by simp)
        | some o₂ =>
          rw [hd2] at hT; simp only [Option.some.injEq] at hT; subst hT
          exact ih₂ o₁.vm hd2 (ih₁ vm hd1 hNA)
  | @rLetU64Zero name body h ih =>
      simp only [translateDialectFull] at hT
      cases hb : translateDialectFull (vm.bind name : VarMap (.sword 64 :: Γ)) body with
      | none => rw [hb] at hT; exact absurd hT (by simp)
      | some ob =>
        rw [hb] at hT; simp only [Option.some.injEq] at hT; subst hT
        exact ih (vm.bind name) hb (noAlias_bind hNA name)
  | @rBlock body h ih =>
      simp only [translateDialectFull] at hT
      exact ih vm hT hNA
  | rCall fname dest args =>
      simp only [translateDialectFull] at hT
      split at hT
      · exact absurd hT (by simp)
      · rename_i ra hra; simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind hNA dest.locVar
  | rSelect dst sel src0 src1 =>
      simp only [translateDialectFull] at hT
      split at hT
      · simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind (noAlias_weaken (noAlias_weaken hNA)) dst.locVar
      · split at hT
        · exact absurd hT (by simp)
        · simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind hNA dst.locVar
  | rCallDstThreaded fname dst args =>
      simp only [translateDialectFull] at hT
      split at hT
      · exact absurd hT (by simp)
      · rename_i ra hra; simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind hNA dst.locVar
  | rTupleLoad dst src idx =>
      simp only [translateDialectFull] at hT
      split at hT
      · exact absurd hT (by simp)
      · rename_i ra hra; simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind hNA dst.locVar
  | rArrLoadLit dst src idx =>
      simp only [translateDialectFull] at hT
      split at hT
      · simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind (noAlias_weaken hNA) dst.locVar
      · split at hT
        · exact absurd hT (by simp)
        · simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind hNA dst.locVar
  | rArrStoreLit arr idx src =>
      simp only [translateDialectFull] at hT
      split at hT
      · simp only [Option.some.injEq] at hT; subst hT
        exact noAlias_bind (noAlias_weaken hNA) arr.locVar
      · split at hT
        · exact absurd hT (by simp)
        · simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind hNA arr.locVar
  | rArrLoad dst src idxVar =>
      simp only [translateDialectFull] at hT
      split at hT <;>
        simp only [Option.some.injEq, reduceCtorEq] at hT <;>
        (subst hT; exact noAlias_bind hNA dst.locVar)
  | rArrStore arr idxVar src =>
      simp only [translateDialectFull] at hT
      split at hT <;>
        simp only [Option.some.injEq, reduceCtorEq] at hT <;>
        (subst hT; exact noAlias_bind hNA arr.locVar)
  | rLimbStore loc idx v =>
      simp only [translateDialectFull] at hT
      cases hlk : vm.lookup loc.locVar with
      | none =>
        rw [hlk] at hT
        dsimp only at hT
        rcases hen : encodeTy loc.locDst with _ | _ | _ | _ | _ | n
        all_goals (rw [hen] at hT; dsimp only at hT)
        iterate 5 (exact absurd hT (by simp))
        by_cases h : idx < n
        · rw [if_pos h] at hT; simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind (noAlias_weaken hNA) loc.locVar
        · rw [if_neg h] at hT; exact absurd hT (by simp)
      | some pair =>
        rw [hlk] at hT
        obtain ⟨ty, arr⟩ := pair
        cases ty with
        | sword _ => exact absurd hT (by simp)
        | bit => exact absurd hT (by simp)
        | unit => exact absurd hT (by simp)
        | pair _ _ => exact absurd hT (by simp)
        | sum _ _ => exact absurd hT (by simp)
        | memref n =>
          simp only at hT
          by_cases h : idx < n
          · rw [dif_pos h] at hT; simp only [Option.some.injEq] at hT; subst hT
            exact noAlias_bind (noAlias_weaken hNA) loc.locVar
          · rw [dif_neg h] at hT; exact absurd hT (by simp)
  | rCallSwap fname dest1 dest2 args =>
      simp only [translateDialectFull] at hT
      cases hMA1 : resolveLocatedArgs vm args with
      | none => rw [hMA1] at hT; exact absurd hT (by simp)
      | some ra =>
        rw [hMA1] at hT
        cases hMA2 : resolveLocatedArgs (vm.bind dest1.locVar) args with
        | none => rw [hMA2] at hT; exact absurd hT (by simp)
        | some ra2 =>
          rw [hMA2] at hT
          simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind (noAlias_bind hNA dest1.locVar) dest2.locVar
  | rCloneCall cv cloneTy oldDest innerF newDest args =>
      simp only [translateDialectFull] at hT
      split at hT
      · rename_i cTy oVar heqLook
        split at hT
        · exact absurd hT (by simp)
        · rename_i ra hra
          simp only [Option.some.injEq] at hT; subst hT
          exact noAlias_bind (noAlias_bind hNA cv) newDest.locVar
      · exact absurd hT (by simp)
  | rCallN fname dests args =>
      simp only [translateDialectFull] at hT
      exact loopCallNDestsD_preserves_noAlias fname args vm dests hT hNA
  | rScalarSetExpr x e =>
      rw [translateDialectFull] at hT
      split at hT
      · exact absurd hT (by simp)
      · next r heqL =>
          obtain ⟨oe, ne, c⟩ := r
          split at hT <;> first
            | (simp only [Option.some.injEq] at hT; subst hT
               exact noAlias_bind (lowerSExpr_preserves_noAlias vm 0 e heqL hNA) _)
            | exact absurd hT (by simp)

/-- The control-flow (`IsCoveredCtl`) front preserves `NoAliasVM`: leaf-covered
    arms delegate to `translateDialectFull_preserves_noAlias`, `RFor` to
    `loopRForD_preserves_noAlias`, each `RIfNz` φ-merge case grows `vm` by
    `bind`/`weaken` steps or a covered re-translation, and `RWhileNz` returns the
    entry `vm` unchanged. -/
theorem translateDialectControl_preserves_noAlias {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (hT : translateDialectControl vm c = some o) (hNA : NoAliasVM vm) : NoAliasVM o.vm := by
  induction hc generalizing Γ vm o with
  | @ofCovered c hcov =>
      rw [translateDialectControl_eq_full_of_covered vm hcov] at hT
      exact translateDialectFull_preserves_noAlias vm hcov hT hNA
  | @rFor x N body hbody ih =>
      simp only [translateDialectControl] at hT
      exact loopRForD_preserves_noAlias
        (translateBodyD := fun vm' => translateDialectControl vm' body) x
        (fun vm'' => ih vm'') vm N hT hNA
  | @rIfNz name thenBr elseBr hthen helse ihthen ihelse =>
      rw [translateDialectControl] at hT
      cases hlk : vm.lookup name with
      | none => rw [hlk] at hT; exact absurd hT (by simp)
      | some sig =>
        obtain ⟨ty, condVar⟩ := sig
        rw [hlk] at hT
        cases ty with
        | bit => exact absurd hT (by simp)
        | unit => exact absurd hT (by simp)
        | pair _ _ => exact absurd hT (by simp)
        | sum _ _ => exact absurd hT (by simp)
        | memref _ => exact absurd hT (by simp)
        | sword w =>
            cases hdt : translateDialectControl vm thenBr with
            | none => rw [hdt] at hT; exact absurd hT (by simp)
            | some o₁ =>
              cases hde : translateDialectControl vm elseBr with
              | none => rw [hdt, hde] at hT; exact absurd hT (by simp)
              | some o₂ =>
                rw [hdt, hde] at hT
                simp only at hT
                by_cases h₁ : o₁.Γ' = Γ
                · by_cases h₂ : o₂.Γ' = Γ
                  · rw [dif_pos h₁, dif_pos h₂] at hT
                    simp only [Option.some.injEq] at hT; subst hT
                    exact ihthen vm hdt hNA
                  · rw [dif_pos h₁, dif_neg h₂] at hT
                    simp only [Option.some.injEq] at hT; subst hT
                    exact ihelse vm hde hNA
                · by_cases h₂ : o₂.Γ' = Γ
                  · rw [dif_neg h₁, dif_pos h₂] at hT
                    simp only [Option.some.injEq] at hT; subst hT
                    exact ihthen vm hdt hNA
                  · rw [dif_neg h₁, dif_neg h₂] at hT
                    cases hss : asSingleScalarSet thenBr with
                    | none =>
                      rw [hss] at hT; simp only at hT
                      cases hr : translateDialectControl o₁.vm elseBr with
                      | none => rw [hr] at hT; exact absurd hT (by simp)
                      | some o₂' =>
                        rw [hr] at hT; simp only [Option.some.injEq] at hT; subst hT
                        exact ihelse o₁.vm hr (ihthen vm hdt hNA)
                    | some thenSet =>
                      cases hse : asSingleScalarSet elseBr with
                      | none =>
                        rw [hss, hse] at hT; simp only at hT
                        cases hr : translateDialectControl o₁.vm elseBr with
                        | none => rw [hr] at hT; exact absurd hT (by simp)
                        | some o₂' =>
                          rw [hr] at hT; simp only [Option.some.injEq] at hT; subst hT
                          exact ihelse o₁.vm hr (ihthen vm hdt hNA)
                      | some elseSet =>
                        rw [hss, hse] at hT; simp only at hT
                        by_cases hN : thenSet.name = elseSet.name
                        · rw [if_pos hN] at hT
                          simp only [Option.some.injEq] at hT; subst hT
                          exact noAlias_bind (noAlias_weaken (noAlias_weaken
                            (noAlias_weaken (noAlias_weaken (noAlias_weaken hNA)))))
                            thenSet.name
                        · rw [if_neg hN] at hT
                          cases hr : translateDialectControl o₁.vm elseBr with
                          | none => rw [hr] at hT; exact absurd hT (by simp)
                          | some o₂' =>
                            rw [hr] at hT; simp only [Option.some.injEq] at hT; subst hT
                            exact ihelse o₁.vm hr (ihthen vm hdt hNA)
  | @rWhileNz name body _hbody _ih =>
      rw [translateDialectControl] at hT
      split at hT
      · cases hb : translateDialectControl vm body with
        | none => rw [hb] at hT; exact absurd hT (by simp)
        | some o' =>
            rw [hb] at hT
            simp only [Option.map_some, Option.some.injEq] at hT
            subst hT
            exact hNA
      · exact absurd hT (by simp)

/-- A 64-bit word pushed onto the valuation under the weakened map keeps the state
    interpretation: every binding of the map refers past the new slot. -/
theorem rustStateInterp_weaken_word {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (w : BitVec 64) :
    RustStateInterp (vm.weaken : VarMap (.sword 64 :: Γ)) rs (HVec.cons w V) := by
  refine ⟨?_, noAlias_weaken hInv.noAlias⟩
  intro name s cv hL
  simp only [VarMap.weaken] at hL
  cases hOld : vm.lookup name with
  | none => rw [hOld] at hL; exact absurd hL (by simp)
  | some pair3 =>
    rw [hOld] at hL
    obtain ⟨t', cv'⟩ := pair3
    simp only [Option.some.injEq, Sigma.mk.injEq] at hL
    obtain ⟨ht', hcvE⟩ := hL
    subst ht'
    cases hcvE
    have hOldOK := hInv name t' cv' hOld
    cases t' with
    | sword nw =>
      by_cases h64 : nw = 64
      · subst h64
        show (CVar.there cv' : CVar (.sword 64 :: Γ) (.sword 64)).lookup (HVec.cons w V)
              = BitVec.ofNat 64 (rs.rsScalar name)
        simp [CVar.lookup]
        exact hOldOK
      · exact bindingOK_sword_ne (n := nw) h64 _ _ _ _
    | memref m =>
      simp only [bindingOK] at hOldOK ⊢
      cases hRsT2 : rs.rsTower name with
      | none => rw [hRsT2] at hOldOK; exact hOldOK
      | some pair4 =>
        rw [hRsT2] at hOldOK
        obtain ⟨t'', vt⟩ := pair4
        intro hEncP
        have hHeqP := hOldOK hEncP
        show HEq ((CVar.there cv' : CVar (.sword 64 :: Γ) (.memref m)).lookup (HVec.cons w V))
                 (cryptoTyOfRustVal t'' vt)
        simp only [CVar.lookup]
        exact hHeqP
    | bit => simp only [bindingOK]
    | unit => simp only [bindingOK]
    | pair _ _ => simp only [bindingOK]
    | sum _ _ => simp only [bindingOK]

/-- **Rust ↔ dialect-front simulation (`CProg`-free statement).**
    On the control-covered fragment `IsCoveredCtl`, if the `CProg`-free direct
    front `translateDialectControl` translates `c` with output `o`, then every
    concrete `RustExec` trace from `rs` to `rs'` (with entry valuation `V`
    satisfying `RustStateInterp vm rs V`) lands a post-state valuation
    `V' : HVec o.Γ'` satisfying `RustStateInterp o.vm rs' V'`.

    Neither the statement nor the proof names `CProg` / `TransOut` / `translate`:
    the proof is a direct induction on the `RustExec` derivation over the dialect
    front, reusing the shared `VarMap`/`RustState` byte-layout transport lemmas. -/
theorem rustExecSimulatesDialect
    {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (hCov : IsCoveredCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (V : HVec Γ) (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' := by
  induction hExec generalizing Γ vm o V with
  | skip rs0 =>
      simp only [translateDialectControl, translateDialectFull, translateDialect,
        Option.some.injEq] at hTrans
      subst hTrans
      exact ⟨V, hInv⟩
  | seq c1 c2 rs0 r1 rs2 _h1 _h2 ih1 ih2 =>
      cases hCov with
      | ofCovered hc =>
        cases hc with
        | rSeq h1c h2c =>
          have h1Ctl : IsCoveredCtl c1 := .ofCovered h1c
          have h2Ctl : IsCoveredCtl c2 := .ofCovered h2c
          -- `translateDialectControl`'s `RSeq` arm now recurses into itself (control
          -- sequencing); case directly on the two child translations.
          simp only [translateDialectControl] at hTrans
          split at hTrans
          · rename_i o₁ hd1
            split at hTrans
            · rename_i o₂ hd2
              simp only [Option.some.injEq] at hTrans
              subst hTrans
              obtain ⟨V₁, hInv₁⟩ := ih1 vm o₁ h1Ctl hd1 V hInv
              obtain ⟨V', hInv'⟩ := ih2 o₁.vm o₂ h2Ctl hd2 V₁ hInv₁
              exact ⟨V', hInv'⟩
            · exact absurd hTrans (by simp)
          · exact absurd hTrans (by simp)
  | letZero x t body rs0 rs2 _h ih => cases hCov with | ofCovered hc => cases hc
  | letU64Zero x body rs0 rs2 _h ih =>
      -- `RLetU64Zero` is core; covered iff body is covered.
      cases hCov with
      | ofCovered hc =>
        cases hc with
        | rLetU64Zero hb =>
          have hbCtl : IsCoveredCtl body := .ofCovered hb
          simp only [translateDialectControl, translateDialectFull] at hTrans
          cases hInner : translateDialectFull (vm.bind x : VarMap (.sword 64 :: Γ)) body with
          | none => rw [hInner] at hTrans; exact absurd hTrans (by simp)
          | some ob =>
            rw [hInner] at hTrans
            simp only [Option.some.injEq] at hTrans
            subst hTrans
            have hInnerCtl : translateDialectControl (vm.bind x) body = some ob := by
              rw [translateDialectControl_eq_full_of_covered _ hb]; exact hInner
            exact ih (vm.bind x) ob hbCtl hInnerCtl
              (HVec.cons (0 : BitVec 64) V) (interp_bind_sword64_zero hInv x)
  | scalarSet x v rs0 =>
      simp only [translateDialectControl, translateDialectFull, translateDialect,
        Option.some.injEq] at hTrans
      subst hTrans
      exact ⟨HVec.cons (BitVec.ofNat 64 v) V,
             interp_bind_sword64_scalarSet hInv x v⟩
  -- `RIfNz` φ-merge arms. The post-branch state `rs2` is reached by executing
  -- one branch; the output `o.vm` is alias-free (`translateDialectControl`
  -- preserves `NoAliasVM`), so the byte-correspondence valuation
  -- `noAlias_canonical_witness` realises `RustStateInterp o.vm rs2` directly —
  -- the same lever the `whileTrue` arm uses for its post-body state.
  | ifTrue e ct cf rs0 rs2 v _heval _hne _hbranch ih =>
      exact ⟨_, noAlias_canonical_witness
        (translateDialectControl_preserves_noAlias vm hCov hTrans hInv.noAlias) rs2⟩
  | ifFalse e ct cf rs0 rs2 _heval _hbranch ih =>
      exact ⟨_, noAlias_canonical_witness
        (translateDialectControl_preserves_noAlias vm hCov hTrans hInv.noAlias) rs2⟩
  -- `RWhileNz` arms. The front's `RWhileNz` output is context-invariant
  -- (`o.Γ' = Γ`, `o.vm = vm`), so the post-loop `VarMap` is alias-free and
  -- `noAlias_canonical_witness` realises `RustStateInterp o.vm` at the post-state
  -- — the same lever the `RIfNz` arms use, and it needs no trip-count argument.
  | whileFalse e body rs0 _heval =>
      exact ⟨_, noAlias_canonical_witness
        (translateDialectControl_preserves_noAlias vm hCov hTrans hInv.noAlias) rs0⟩
  | whileTrue e body rs0 r1 rs2 v _heval _hne _hbody _hnext ih1 ih2 =>
      exact ⟨_, noAlias_canonical_witness
        (translateDialectControl_preserves_noAlias vm hCov hTrans hInv.noAlias) rs2⟩
  | forZero x body rs0 =>
      simp only [translateDialectControl, loopRForD, Option.some.injEq] at hTrans
      subst hTrans
      exact ⟨V, hInv⟩
  | forSucc x n body rs0 r1 rs2 _hbody _hstep ih1 ih2 =>
      cases hCov with
      | ofCovered hc => cases hc
      | rFor hbodyCov =>
        simp only [translateDialectControl, loopRForD] at hTrans
        cases hPre : loopRForD (fun {Γ''} vm' => translateDialectControl vm' body) vm x n with
        | none => rw [hPre] at hTrans; exact absurd hTrans (by simp)
        | some oPre =>
          rw [hPre] at hTrans
          simp only at hTrans
          cases hBody : translateDialectControl (oPre.vm.bind x) body with
          | none => rw [hBody] at hTrans; exact absurd hTrans (by simp)
          | some oBody =>
            rw [hBody] at hTrans
            simp only [Option.some.injEq] at hTrans
            subst hTrans
            have hPreTrans : translateDialectControl vm (.RFor x n body) = some oPre := by
              simp only [translateDialectControl]; exact hPre
            obtain ⟨V1, hInv1⟩ := ih1 vm oPre (.rFor hbodyCov) hPreTrans V hInv
            have hInvBind := interp_bind_sword64_scalarSet hInv1 x n
            exact ih2 (oPre.vm.bind x) oBody hbodyCov hBody _ hInvBind
  | forRuntime x bound body rs0 rs2 _hInner _ih =>
      -- The runtime loop is not in the covered/translatable fragment.
      cases hCov with | ofCovered hc => cases hc
  | call f dest args rs0 oldDestV argList _hLook _hArgs =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · exact absurd hTrans (by simp)
      · rename_i ra hra
        simp only [Option.some.injEq] at hTrans
        subst hTrans
        obtain ⟨destVar, destSrc⟩ := dest
        cases destSrc with
        | TU64 =>
            refine ⟨HVec.cons (BitVec.ofNat 64 (rs0.rsScalar destVar)) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TU64,
                leafSpec.call f .TU64 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_sword64_setTowerTU64_general (x := destVar) hInv _
        | TFp =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp
                (leafSpec.call f .TFp (args.map (·.locDst)) oldDestV argList) :
                Fin 6 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp,
                leafSpec.call f .TFp (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp (n := 6) rfl _
        | TFp2 =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp2
                (leafSpec.call f .TFp2 (args.map (·.locDst)) oldDestV argList) :
                Fin 12 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp2,
                leafSpec.call f .TFp2 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp2 (n := 12) rfl _
        | TFp6 =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp6
                (leafSpec.call f .TFp6 (args.map (·.locDst)) oldDestV argList) :
                Fin 36 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp6,
                leafSpec.call f .TFp6 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp6 (n := 36) rfl _
        | TFp12 =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp12
                (leafSpec.call f .TFp12 (args.map (·.locDst)) oldDestV argList) :
                Fin 72 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp12,
                leafSpec.call f .TFp12 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp12 (n := 72) rfl _
        | TFp25519 =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp25519
                (leafSpec.call f .TFp25519 (args.map (·.locDst)) oldDestV argList) :
                Fin 5 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp25519,
                leafSpec.call f .TFp25519 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp25519 (n := 5) rfl _
        | TFp25519_64 =>
            refine ⟨HVec.cons
              (cryptoTyOfRustVal .TFp25519_64
                (leafSpec.call f .TFp25519_64 (args.map (·.locDst)) oldDestV argList) :
                Fin 4 → BitVec 64) V, ?_⟩
            show RustStateInterp _
              (rsSetTower rs0 destVar ⟨.TFp25519_64,
                leafSpec.call f .TFp25519_64 (args.map (·.locDst)) oldDestV argList⟩) _
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFp25519_64 (n := 4) rfl _
        | TFpL25519 =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFpL25519 rfl _
        | TFpP256 =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TFpP256 rfl _
        | TFp25519_4Bounded b =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TFp25519_4Bounded b) rfl _
        | TFpGen nm sz =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TFpGen nm sz) rfl _
        | TFp2Gen nm sz =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TFp2Gen nm sz) rfl _
        | TTuple a b =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TTuple a b) rfl _
        | TBytes n =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TBytes n) rfl _
        | TArr n t =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TArr n t) rfl _
        | TPolyMod q n =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TPolyMod q n) rfl _
        | TPolyVec q n k =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TPolyVec q n k) rfl _
        | TPolyMat q n k m =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    (.TPolyMat q n k m) rfl _
        | TU8 =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TU8 rfl _
        | TU32 =>
            refine ⟨HVec.cons (CryptoTy.default _) V, ?_⟩
            exact interp_bind_memref_setTower_general (x := destVar) hInv
                    .TU32 rfl _
  | cloneCall cv ct oldD innerF dest args rs0 rsClone rs2 _hClone _hInner ih =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · rename_i cloneTy oldVar heqLook
        split at hTrans
        · exact absurd hTrans (by simp)
        · rename_i ra hra
          simp only [Option.some.injEq] at hTrans
          subst hTrans
          subst _hClone
          obtain ⟨w, hInvClone⟩ := interp_cons_setTower_any hInv cv cloneTy
                                    ((rs0.rsTower oldD.locVar).getD ⟨ct, default⟩)
          cases _hInner
          rename_i argList oldDestV _hLook _hArgs _hArgsTyped
          obtain ⟨destVar, destSrc⟩ := dest
          cases destSrc with
          | TU64 =>
              refine ⟨HVec.cons (BitVec.ofNat 64
                                  ((rsSetTower rs0 cv ((rs0.rsTower oldD.locVar).getD
                                    ⟨ct, default⟩)).rsScalar destVar))
                                (HVec.cons w V), ?_⟩
              exact interp_bind_sword64_setTowerTU64_general
                      (x := destVar) hInvClone _
          | TFp =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp
                  (leafSpec.call innerF .TFp (args.map (·.locDst)) oldDestV argList) :
                  Fin 6 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp (n := 6) rfl _
          | TFp2 =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp2
                  (leafSpec.call innerF .TFp2 (args.map (·.locDst)) oldDestV argList) :
                  Fin 12 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp2 (n := 12) rfl _
          | TFp6 =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp6
                  (leafSpec.call innerF .TFp6 (args.map (·.locDst)) oldDestV argList) :
                  Fin 36 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp6 (n := 36) rfl _
          | TFp12 =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp12
                  (leafSpec.call innerF .TFp12 (args.map (·.locDst)) oldDestV argList) :
                  Fin 72 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp12 (n := 72) rfl _
          | TFp25519 =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp25519
                  (leafSpec.call innerF .TFp25519 (args.map (·.locDst)) oldDestV argList) :
                  Fin 5 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp25519 (n := 5) rfl _
          | TFp25519_64 =>
              refine ⟨HVec.cons
                (cryptoTyOfRustVal .TFp25519_64
                  (leafSpec.call innerF .TFp25519_64 (args.map (·.locDst)) oldDestV argList) :
                  Fin 4 → BitVec 64) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFp25519_64 (n := 4) rfl _
          | TFpL25519 =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFpL25519 rfl _
          | TFpP256 =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TFpP256 rfl _
          | TFp25519_4Bounded b =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TFp25519_4Bounded b) rfl _
          | TFpGen nm sz =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TFpGen nm sz) rfl _
          | TFp2Gen nm sz =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TFp2Gen nm sz) rfl _
          | TTuple a b =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TTuple a b) rfl _
          | TBytes n =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TBytes n) rfl _
          | TArr n t =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TArr n t) rfl _
          | TPolyMod q n =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TPolyMod q n) rfl _
          | TPolyVec q n k =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TPolyVec q n k) rfl _
          | TPolyMat q n k m =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      (.TPolyMat q n k m) rfl _
          | TU8 =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TU8 rfl _
          | TU32 =>
              refine ⟨HVec.cons (CryptoTy.default _) (HVec.cons w V), ?_⟩
              exact interp_bind_memref_setTower_general (x := destVar) hInvClone
                      .TU32 rfl _
      · exact absurd hTrans (by simp)
  | limbStore loc idx vbv rs0 oldDestV _hLook =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      cases hLook : vm.lookup loc.locVar with
      | none =>
        rw [hLook] at hTrans
        dsimp only at hTrans
        rcases hEnc : encodeTy loc.locDst with _ | _ | _ | _ | _ | n
        all_goals (rw [hEnc] at hTrans; dsimp only at hTrans)
        iterate 5 (exact absurd hTrans (by simp))
        by_cases h : idx < n
        · rw [if_pos h] at hTrans
          simp only [Option.some.injEq] at hTrans
          subst hTrans
          simp only [locatedUpdate]
          exact ⟨_, interp_bind_memref_setTower_general (x := loc.locVar)
            (rustStateInterp_weaken_word hInv vbv) loc.locDst hEnc
            (leafSpec.limbStore loc oldDestV idx vbv)⟩
        · rw [if_neg h] at hTrans
          exact absurd hTrans (by simp)
      | some pair =>
        rw [hLook] at hTrans
        obtain ⟨t, arr⟩ := pair
        cases t with
        | sword _ => exact absurd hTrans (by simp)
        | bit => exact absurd hTrans (by simp)
        | unit => exact absurd hTrans (by simp)
        | pair _ _ => exact absurd hTrans (by simp)
        | sum _ _ => exact absurd hTrans (by simp)
        | memref n =>
          simp only at hTrans
          by_cases h : idx < n
          · rw [dif_pos h] at hTrans
            simp only [Option.some.injEq] at hTrans
            subst hTrans
            have hOK := hInv loc.locVar (.memref n) arr hLook
            have hRsT : rs0.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ := by
              unfold locatedLookup at _hLook
              cases hT : rs0.rsTower loc.locVar with
              | none => rw [hT] at _hLook; exact absurd _hLook (by simp)
              | some pair2 =>
                rw [hT] at _hLook
                obtain ⟨t', vt⟩ := pair2
                simp only at _hLook
                split_ifs at _hLook with htEq
                subst htEq
                simp only [Option.some.injEq] at _hLook
                subst _hLook
                rfl
            simp only [bindingOK] at hOK
            rw [hRsT] at hOK
            have hInvW := rustStateInterp_weaken_word hInv vbv
            simp only [locatedUpdate]
            by_cases hEnc : encodeTy loc.locDst = .memref n
            · exact ⟨_, interp_bind_memref_setTower_general (x := loc.locVar) hInvW
                      loc.locDst hEnc
                      (leafSpec.limbStore loc oldDestV idx vbv)⟩
            · refine ⟨HVec.cons (fun _ => 0 : Fin n → BitVec 64) (HVec.cons vbv V), ?_,
                      noAlias_bind hInvW.noAlias loc.locVar⟩
              intro nm s cv hLook
              simp only [VarMap.bind] at hLook
              by_cases hN2 : nm = loc.locVar
              · subst hN2
                rw [if_pos rfl] at hLook
                simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
                obtain ⟨hs, hcv⟩ := hLook
                subst hs
                cases hcv
                simp only [bindingOK]
                rw [rsSetTower_same rs0 loc.locVar
                      ⟨loc.locDst, leafSpec.limbStore loc oldDestV idx vbv⟩]
                intro hAbs
                exact absurd hAbs hEnc
              · rw [if_neg hN2] at hLook
                cases hOld : (vm.weaken : VarMap (.sword 64 :: Γ)).lookup nm with
                | none => rw [hOld] at hLook; exact absurd hLook (by simp)
                | some pair5 =>
                  rw [hOld] at hLook
                  obtain ⟨t', cv'⟩ := pair5
                  simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
                  obtain ⟨ht', hcvE⟩ := hLook
                  subst ht'
                  cases hcvE
                  exact bindingOK_there_setTower (s := .memref n) cv'
                          (fun _ => 0 : Fin n → BitVec 64)
                          ⟨loc.locDst, leafSpec.limbStore loc oldDestV idx vbv⟩
                          hN2 (hInvW nm t' cv' hOld)
          · rw [dif_neg h] at hTrans
            exact absurd hTrans (by simp)
  | callN f dests args rs0 argList _hArgList _hArgs _hDests =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      exact loopCallNDestsD_interp_extend leafSpec f args (args.map (·.locDst)) argList
        hInv dests 0 hTrans
  | callDstThreaded f dst args rs0 oldDestV argList _hLook _hArgs _hArgsTyped =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · exact absurd hTrans (by simp)
      · rename_i ra hra
        simp only [Option.some.injEq] at hTrans
        subst hTrans
        simp only [locatedUpdate]
        obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
          ⟨dst.locDst, leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList⟩
        exact ⟨HVec.cons w V, hInv'⟩
  -- The word comparison select binds two anonymous temporaries and the destination;
  -- its post-state valuation is the canonical witness of the alias-free `VarMap`.
  -- Any other select is one opaque leaf binding.
  | selectFalse dst sel src0 src1 rs0 hTy srcV _hSel _hLook =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · simp only [Option.some.injEq] at hTrans
        subst hTrans
        exact ⟨_, noAlias_canonical_witness (noAlias_bind (noAlias_weaken
          (noAlias_weaken hInv.noAlias)) dst.locVar) _⟩
      · split at hTrans
        · exact absurd hTrans (by simp)
        · simp only [Option.some.injEq] at hTrans
          subst hTrans
          simp only [locatedUpdate]
          obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
            ⟨dst.locDst, hTy ▸ srcV⟩
          exact ⟨HVec.cons w V, hInv'⟩
  | selectTrue dst sel src0 src1 rs0 hTy v srcV _hSel _hNe _hLook =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · simp only [Option.some.injEq] at hTrans
        subst hTrans
        exact ⟨_, noAlias_canonical_witness (noAlias_bind (noAlias_weaken
          (noAlias_weaken hInv.noAlias)) dst.locVar) _⟩
      · split at hTrans
        · exact absurd hTrans (by simp)
        · simp only [Option.some.injEq] at hTrans
          subst hTrans
          simp only [locatedUpdate]
          obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
            ⟨dst.locDst, hTy ▸ srcV⟩
          exact ⟨HVec.cons w V, hInv'⟩
  | assert label rs0 =>
      simp only [translateDialectControl, translateDialectFull, Option.some.injEq] at hTrans
      subst hTrans
      exact ⟨V, hInv⟩
  | block body rs0 rs2 _hbody ih =>
      cases hCov with
      | ofCovered hc =>
        cases hc with
        | rBlock hb =>
          have hbCtl : IsCoveredCtl body := .ofCovered hb
          have hTrBody : translateDialectControl vm body = some o := by
            rw [translateDialectControl_eq_full_of_covered vm hb]
            simpa [translateDialectControl, translateDialectFull] using hTrans
          exact ih vm o hbCtl hTrBody V hInv
  | tupleLoad dst src idx rs0 oldV srcV _hLookDst _hLookSrc =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · exact absurd hTrans (by simp)
      · rename_i ra hra
        simp only [Option.some.injEq] at hTrans
        subst hTrans
        simp only [locatedUpdate]
        obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
          ⟨dst.locDst, leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx⟩
        exact ⟨HVec.cons w V, hInv'⟩
  | arrStore arr idxVar src rs0 idx oldV srcV _h1 _h2 _h3 =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans <;>
        simp only [Option.some.injEq, reduceCtorEq] at hTrans <;>
        (subst hTrans
         simp only [locatedUpdate]
         obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv arr.locVar (encodeTy arr.locDst)
           ⟨arr.locDst, leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩⟩
         exact ⟨HVec.cons w V, hInv'⟩)
  | arrLoad dst src idxVar rs0 idx oldV srcV _h1 _h2 _h3 =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans <;>
        simp only [Option.some.injEq, reduceCtorEq] at hTrans <;>
        (subst hTrans
         simp only [locatedUpdate]
         obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
           ⟨dst.locDst, leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx⟩
         exact ⟨HVec.cons w V, hInv'⟩)
  -- The literal-index access to a `TArr _ .TU64` word array binds an anonymous index
  -- temporary and the destination; its post-state valuation is the canonical witness
  -- of the alias-free `VarMap`. Any other shape, a byte or `u32` array included, is
  -- one opaque leaf binding.
  | arrStoreLit arr idx src rs0 oldV srcV _hLookArr _hLookSrc =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · simp only [Option.some.injEq] at hTrans
        subst hTrans
        exact ⟨_, noAlias_canonical_witness
          (noAlias_bind (noAlias_weaken hInv.noAlias) arr.locVar) _⟩
      · split at hTrans
        · exact absurd hTrans (by simp)
        · simp only [Option.some.injEq] at hTrans
          subst hTrans
          simp only [locatedUpdate]
          obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv arr.locVar (encodeTy arr.locDst)
            ⟨arr.locDst, leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩⟩
          exact ⟨HVec.cons w V, hInv'⟩
  | arrLoadLit dst src idx rs0 oldV srcV _hLookDst _hLookSrc =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      split at hTrans
      · simp only [Option.some.injEq] at hTrans
        subst hTrans
        exact ⟨_, noAlias_canonical_witness
          (noAlias_bind (noAlias_weaken hInv.noAlias) dst.locVar) _⟩
      · split at hTrans
        · exact absurd hTrans (by simp)
        · simp only [Option.some.injEq] at hTrans
          subst hTrans
          simp only [locatedUpdate]
          obtain ⟨w, hInv'⟩ := interp_cons_setTower_any hInv dst.locVar (encodeTy dst.locDst)
            ⟨dst.locDst, leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx⟩
          exact ⟨HVec.cons w V, hInv'⟩
  | limbStoreExpr loc idx e rs0 oldDestV _hLook =>
      cases hCov with | ofCovered hc => cases hc
  | scalarSetExpr x e rs0 =>
      -- `RScalarSetExpr` is covered; the front is `NoAliasVM`-preserving, so the
      -- post-state (the scalar overwrite) is realised by the canonical
      -- byte-correspondence witness at `o.vm` (the same lever the `RIfNz`/`while`
      -- arms use). The simulation is existential, so this needs only
      -- `NoAliasVM o.vm`, not the SSA-emitted denotation.
      have hNAo : NoAliasVM o.vm :=
        translateDialectControl_preserves_noAlias vm hCov hTrans hInv.noAlias
      exact ⟨_, noAlias_canonical_witness hNAo (rsSetScalar rs0 x (e.evalState rs0))⟩
  | callSwap fname dest1 dest2 args rsCS rs1CS rs'CS _h1 _h2 ih1 ih2 =>
      simp only [translateDialectControl, translateDialectFull] at hTrans
      cases hMA1 : resolveLocatedArgs vm args with
      | none => rw [hMA1] at hTrans; exact absurd hTrans (by simp)
      | some resolvedArgs =>
        rw [hMA1] at hTrans
        cases hMA2 : resolveLocatedArgs (vm.bind dest1.locVar) args with
        | none => rw [hMA2] at hTrans; exact absurd hTrans (by simp)
        | some resolvedArgs2 =>
          rw [hMA2] at hTrans
          simp only [Option.some.injEq] at hTrans
          subst hTrans
          have hC1 : IsCoveredCtl (.RCall fname dest1 args) :=
            .ofCovered (.rCall fname dest1 args)
          have hC2 : IsCoveredCtl (.RCall fname dest2 args) :=
            .ofCovered (.rCall fname dest2 args)
          have ho1 : translateDialectControl vm (.RCall fname dest1 args)
              = some { Γ' := encodeTy dest1.locDst :: Γ,
                       cont := fun {_t} =>
                         ComCont.varBind (extCallExpr fname (encodeTy dest1.locDst)
                           (listSigmaToCHVector resolvedArgs).snd),
                       vm := vm.bind dest1.locVar } := by
            simp only [translateDialectControl, translateDialectFull, hMA1]
          have ho2 : translateDialectControl (vm.bind dest1.locVar) (.RCall fname dest2 args)
              = some { Γ' := encodeTy dest2.locDst :: encodeTy dest1.locDst :: Γ,
                       cont := fun {_t} =>
                         ComCont.varBind (extCallExpr fname (encodeTy dest2.locDst)
                           (listSigmaToCHVector resolvedArgs2).snd),
                       vm := (vm.bind dest1.locVar).bind dest2.locVar } := by
            simp only [translateDialectControl, translateDialectFull, hMA2]
          obtain ⟨V1, hInv1⟩ := ih1 vm _ hC1 ho1 V hInv
          obtain ⟨V', hInv'⟩ := ih2 (vm.bind dest1.locVar) _ hC2 ho2 V1 hInv1
          exact ⟨V', hInv'⟩

/-- **Rust ↔ dialect simulation for the data-dependent loop `RWhileNz`.**
    The `RWhileNz` specialization of `rustExecSimulatesDialect`, in the shape of
    `RForPreservation.loopRForD_denotation_preserved`: for a loop whose body is
    control-covered and whose front output is `o`, every `RustExec` run of the
    loop lands a post-state valuation satisfying `RustStateInterp o.vm`.

    The trip count is not a parameter and no fuel or termination hypothesis is
    needed: `hExec` is a finite `RustExec` derivation, and the front's `RWhileNz`
    output is context-invariant (`o.Γ' = Γ`, `o.vm = vm`), so the post-loop
    interpretation is the alias-free canonical witness at the entry `VarMap`.
    This is state-correspondence at the loop boundary, not a statement that the
    dialect prefix recomputes the loop's result. -/
theorem rustExecSimulatesDialect_RWhileNz {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (body : LowCT) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (hCov : IsCoveredCtl body)
    (hTrans : translateDialectControl vm (.RWhileNz name body) = some o)
    (hExec : RustExec N leafSpec (.RWhileNz name body) rs rs')
    (V : HVec Γ) (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' :=
  rustExecSimulatesDialect vm (.RWhileNz name body) o N leafSpec rs rs'
    (.rWhileNz hCov) hTrans hExec V hInv

/-- **Rust ↔ dialect simulation for the vector node `RVsimdSetExpr`.**
    `RVsimdSetExpr x tag args` is definitionally a reserved-tag `RCall`, so it is
    `IsCoveredCtl` (`ofCovered ∘ rCall`) and its Rust ↔ dialect simulation is the
    `RCall` case of `rustExecSimulatesDialect`: every concrete `RustExec` trace of
    the node (an opaque data-oblivious leaf — the 128-bit vector value lives
    outside the `TowerType`-modeled `RustState`; the SIMD lane semantics is pinned
    at the dialect `denote = spec` level) lands a post-state valuation satisfying
    the output `RustStateInterp`. Direct corollary — no new induction. -/
theorem rustExecSimulatesDialect_RVsimdSetExpr {Γ : Ctx} (vm : VarMap Γ)
    (x tag : String) (args : List String) (o : DTransOut Γ)
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (hTrans : translateDialectControl vm (LowCT.RVsimdSetExpr x tag args) = some o)
    (hExec : RustExec N leafSpec (LowCT.RVsimdSetExpr x tag args) rs rs')
    (V : HVec Γ) (hInv : RustStateInterp vm rs V) :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' :=
  rustExecSimulatesDialect vm _ o N leafSpec rs rs'
    (.ofCovered (.rCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩))))
    hTrans hExec V hInv

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
