/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted

/-!
# Source adequacy of the rolled-loop body front

`TranslateDialectRolledLoop.frontLoopBodyJ` front-compiles one `LowCT` loop body
to the `JLoopBodyN.update`-shaped `Com jasminDialect` that the `ComL` loop nodes
consume. The per-shape `rolledForLoop*_denote` lemmas take
`frontLoopBodyJ … = some update` as a hypothesis and conclude at
`JLoopBodyN.denote` of that `update`, so their statements are about the
compiler's own output.

This module relates `update` back to the source. The two legs of the relation
are `TranslateDialectScalar.translateDialectControl_denote_ctl` (front
preservation over `IsCoveredSCtl`, against the `semScalar` waist) and
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'` (the A1
lowering transport), already composed in
`CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq`. What that
composite is stated over is a translation output `o : DTransOut Γ` together with
the four success facts `hTrans` / `hName` / `hRet` / `hCom`. `frontLoopBodyJ`
packages exactly those four into one `Option` pipeline, so the bridge here
destructures a single `frontLoopBodyJ … = some update` into them and reads the
composite off.

```
  semScalar body env = some env'          -- source semantics
  env' accName = some ⟨accCTy, accval⟩    -- the accumulator the loop carries
  ────────────────────────────────────────────────────────────────
  update.denote (ctMapValD V) = ctTransTy accval
```

## The residual side condition

`frontLoopBodyJ … = some update` remains a hypothesis, with `update`
universally quantified: it names the compiler's output rather than asserting
anything about it. It is not derivable from `IsCoveredSCtl`, because neither leg
is a totality result — `translateDialectControl_denote_ctl` assumes front
success and `cryptoDialectToJasminCom_denote_eq'` assumes lowering success. Each
deployed kernel discharges it by evaluation on its own concrete body;
`frontLoopBodyJ_denote_of_isSome` is the form that takes the decidable
`(frontLoopBodyJ …).isSome` instead and produces the `= some update` equation
along with the adequacy.

## Main results

* `frontLoopBodyJ_denote` — the front-compiled loop body's jasmin denotation is
  the transported value the source `LowCT` body's `semScalar` run leaves in the
  accumulator name.
* `frontLoopBodyJ_denote_of_isSome` — the same over `(frontLoopBodyJ …).isSome`,
  producing the `= some update` equation the `rolledForLoop*_denote` lemmas take
  as a hypothesis.

`X86Backend.MpnLogicalFrontDenote` applies these to the `mpn_and_n` loop body.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
  (semScalarToJasminCom_denote_eq)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredSCtl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyCD frontLoopBodyJ frontLoopBodyJ_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The `frontLoopBodyJ` pipeline destructured

`frontLoopBodyCD` is a three-stage `Option` match — front success, accumulator
lookup at the post-varmap, continuation application to `ret accName` — and
`frontLoopBodyJ` caps it with the A1 lowering. Inverting a success gives back
exactly the four premises `semScalarToJasminCom_denote_eq` takes. -/

/-- Inversion of a `frontLoopBodyCD` success: the front ran to some `o`, the
    post-varmap resolves `accName` to a slot at the accumulator type, and the
    continuation accepted `ret` of that slot. -/
theorem frontLoopBodyCD_inv {Γbody : Ctx} {accCTy : CryptoTy}
    {vmBody : VarMap Γbody} {accName : String} {body : LowCT}
    {com : Com catCryptDialect Γbody accCTy}
    (h : frontLoopBodyCD (accCTy := accCTy) vmBody accName body = some com) :
    ∃ (o : DTransOut Γbody) (w : CVar o.Γ' accCTy),
      translateDialectControl vmBody body = some o ∧
      o.vm.lookup accName = some ⟨accCTy, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com := by
  unfold frontLoopBodyCD at h
  split at h
  · rename_i o htr
    split at h
    · rename_i t w hlk
      split at h
      · rename_i hty
        subst hty
        exact ⟨o, w, htr, hlk, h⟩
      · simp at h
    · simp at h
  · simp at h

/-! ## 2. Source adequacy of the front-compiled loop body -/

/-- **The front-compiled loop body computes the source accumulator.** For an
    `IsCoveredSCtl` body, an entry valuation consistent with the entry
    environment, and a `semScalar` run leaving `accval` in `accName`, the
    `JLoopBodyN.update`-shaped jasmin program the loop-body front emits denotes
    `ctTransTy accval`.

    `update` is universally quantified, so `hupd` names the compiler's output
    without asserting anything about it; the content of the theorem is the
    equation between that output's denotation and the source value.

    The proof inverts the `frontLoopBodyJ` pipeline into the four success facts
    `semScalarToJasminCom_denote_eq` takes and applies it. -/
theorem frontLoopBodyJ_denote {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γbody)
    (env env' : SEnvScalar) (accval : ⟦accCTy⟧)
    (hc : ConsistentS vmBody V env)
    (hsem : semScalar body env = some env')
    (hval : env' accName = some ⟨accCTy, accval⟩)
    {update : Com jasminDialect (mapCtx Γbody) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update) :
    update.denote (ctMapValD V) = ctTransTy accval := by
  rw [frontLoopBodyJ_eq] at hupd
  split at hupd
  · rename_i com hcd
    obtain ⟨o, w, htr, hlk, hret⟩ := frontLoopBodyCD_inv hcd
    exact semScalarToJasminCom_denote_eq vmBody body o V env env' accName w accval
      com update hcov htr hc hsem hlk hval hret hupd
  · simp at hupd

/-- **The same over the decidable front-success gate.** Taking
    `(frontLoopBodyJ …).isSome` in place of a named output produces both the
    `= some update` equation the `rolledForLoop*_denote` lemmas take as a
    hypothesis and that output's source adequacy. -/
theorem frontLoopBodyJ_denote_of_isSome {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (hcov : IsCoveredSCtl body)
    (V : Ctxt.Valuation (d := catCryptDialect) Γbody)
    (env env' : SEnvScalar) (accval : ⟦accCTy⟧)
    (hc : ConsistentS vmBody V env)
    (hsem : semScalar body env = some env')
    (hval : env' accName = some ⟨accCTy, accval⟩)
    (hJ : (frontLoopBodyJ (accCTy := accCTy) vmBody accName body).isSome) :
    ∃ update : Com jasminDialect (mapCtx Γbody) (mapTy accCTy),
      frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update ∧
      update.denote (ctMapValD V) = ctTransTy accval := by
  obtain ⟨update, hupd⟩ := Option.isSome_iff_exists.mp hJ
  exact ⟨update, hupd,
    frontLoopBodyJ_denote vmBody accName body hcov V env env' accval hc hsem hval hupd⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote
