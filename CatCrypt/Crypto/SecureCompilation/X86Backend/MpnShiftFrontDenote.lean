/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The `mpn_lshift` / `mpn_rshift` loop body against its source semantics

`MpnShiftFrontEmit.shiftRtProg_denote` states the emitted runtime-trip loop's
denotation as the `JLoopBodyN` fold of `update`, under the hypothesis
`frontLoopBodyJ … = some update`. This module supplies that `update`, runs the
source `LowCT` funnel body symbolically through `semScalar` from the canonical
per-trip entry state, and identifies each trip with the word-model step
`shiftFoldStep` — so the model-level value theorems `shiftFold_val` /
`lshiftFold_val` / `rshiftFold_val` read on the compiled program's denotation.

The per-trip run is the finite per-command check: two `RArrLoad`s (the spill-in
cell, the source limb), four `RScalarSetExpr`s (the complementary shift amount,
the shifted limb, the spill-out, the merge) and two `RArrStore`s, each stepped by
the waist lemmas of `Secp256k1PointOpFrameRoundTrip`. The one new word identity
it needs is `shb_toNat`: the complementary shift `64 - sh` computed in the word
model coincides with the `SSub (SLit 64) (SVar "sh")` the body evaluates, for a
shift amount at most `64`.

## Main results

* `shiftBody_covered` — the funnel body is covered straight-line `LowCT`.
* `shiftUpdate` / `shiftUpdate_eq` — the front-compiled funnel body and the
  equation discharging `shiftRtProg_denote`'s hypothesis.
* `shiftLimbBody_run` — the per-trip `semScalar` run: from the canonical entry
  state at trip `t`, the body leaves `shiftFoldStep up sh acc t` in `rp`.
* `shiftRtProg_fold` — the runtime-trip program's denotation is the `shiftFold`
  word-model fold, with no remaining hypothesis.
* `shiftRtProg_val`, `lshiftRtProg_val`, `rshiftRtProg_val` — the machine-level
  value theorems: the compiled program's output cells recombine via `bignumVal`
  to the funnel-shift contract in its three readings.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredS IsCoveredSCtl srcClean isTmpName
   envReadU64 envReader semLowerSExpr binNode consistentS_empty)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC
  (consistentS_bind frontLoopBodyJ_denote_foldl)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (upd_ne upd_self envReadU64_of_bound envReader_of_bound envReadU64_upd_ne
   envReadU64_upd_self semScalar_arrLoad semScalar_arrStore semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Ascent (notTmp_of_short)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells seqAll)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step lower_add_vv lower_add_lit)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once — the `by decide` on
the below-`4` name length is paid a single time per name — and referenced at the
freshness sites below, instead of re-deciding the string length at each site. -/
theorem nt_cy : ¬ isTmpName "cy" := notTmp_of_short _ (by decide)
theorem nt_hi : ¬ isTmpName "hi" := notTmp_of_short _ (by decide)
theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_lo : ¬ isTmpName "lo" := notTmp_of_short _ (by decide)
theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
theorem nt_sh : ¬ isTmpName "sh" := notTmp_of_short _ (by decide)
theorem nt_shb : ¬ isTmpName "shb" := notTmp_of_short _ (by decide)
theorem nt_t : ¬ isTmpName "t" := notTmp_of_short _ (by decide)

/-! ## 1. Progress of the three new `SExpr` shapes the funnel body uses -/

/-- Progress of the funnel left shift `t << sh`, both operands source reads. -/
theorem lower_shl_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SShl (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- Progress of the funnel right shift `t >> shb`, both operands source reads. -/
theorem lower_shr_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SShr (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- Progress of the complementary-shift step `64 - sh`, a literal minus a source
    read. -/
theorem lower_lit_sub_var {env : SEnvScalar} {y : String} {wy : BitVec 64} (L : Nat)
    (hy : envReadU64 env y = some wy) (hyl : y.length < 4) :
    (semLowerSExpr env 0 (.SSub (.SLit L) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hy, binNode, envReadU64_upd_ne (ne_tmp_of_short hyl 0),
    envReadU64_upd_self]
  rfl

/-! ## 2. The complementary-shift word identity -/

/-- The word-model complementary shift `64 - sh` equals the `toNat` of the
    body's `SSub (SLit 64) (SVar "sh")` value `BitVec.ofNat 64 64 - shVal`, for a
    shift amount at most `64`. -/
theorem shb_toNat (shVal : BitVec 64) (h : shVal.toNat ≤ 64) :
    (BitVec.ofNat 64 64 - shVal).toNat = 64 - shVal.toNat := by
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have hrw : 2 ^ 64 - shVal.toNat + 64 % (2 ^ 64) = 2 ^ 64 + (64 - shVal.toNat) := by
    rw [Nat.mod_eq_of_lt (show (64 : Nat) < 2 ^ 64 by norm_num)]; omega
  rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! ## 3. The canonical per-trip entry state -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of the funnel body at one trip: the output
    array at `rp`, the trip index at `idx`, the source array at `up`, the scalar
    shift amount at `sh`. -/
def shiftEnv (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) : SEnvScalar :=
  ((((emptyEnv.upd "sh" (t := .sword 64) sh).upd
      "up" (t := .memref NUS) up).upd
      "idx" (t := .sword 64) iv).upd "rp" (t := .memref NRS) acc)

/-- The canonical entry state is consistent with `vmBody` and the trip
    valuation. -/
theorem consistentS_shiftEnv (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons up (.cons sh .nil)))) (shiftEnv up sh acc iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    consistentS_empty "sh" (t := .sword 64) sh) "up" (t := .memref NUS) up)
    "idx" (t := .sword 64) iv) "rp" (t := .memref NRS) acc

theorem shiftEnv_rp (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) :
    shiftEnv up sh acc iv "rp" = some ⟨.memref NRS, acc⟩ := upd_self _ _ _

theorem shiftEnv_idx (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) :
    shiftEnv up sh acc iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [shiftEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem shiftEnv_up (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) :
    shiftEnv up sh acc iv "up" = some ⟨.memref NUS, up⟩ := by
  rw [shiftEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem shiftEnv_sh (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (acc : Fin NRS → BitVec 64) (iv : BitVec 64) :
    shiftEnv up sh acc iv "sh" = some ⟨.sword 64, sh⟩ := by
  rw [shiftEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 4. The per-trip run of the funnel body -/

/-- **The funnel body computes one `shiftFoldStep`.** From the canonical entry
    state at trip `t`, with a shift amount at most `64`, the source body's
    `semScalar` run terminates and leaves exactly the word-model step's array in
    `rp`: the merged output word at cell `t` and the spill-out at cell `t + 1`.
    The per-command check of the seam, stepped through the nine commands. -/
theorem shiftLimbBody_run (up : Fin NUS → BitVec 64) (shVal : BitVec 64)
    (acc : Fin NRS → BitVec 64) (t : Nat) (hsh : shVal.toNat ≤ 64) (ht : t + 1 < 2 ^ 64) :
    ∃ env', semScalar shiftBodyLowCT (shiftEnv up shVal acc (BitVec.ofNat 64 t)) = some env'
      ∧ env' "rp" = some ⟨.memref NRS, shiftFoldStep up shVal.toNat acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by
    simp only [hivdef, BitVec.toNat_ofNat]
    omega
  have hiv1N : (iv + BitVec.ofNat 64 1).toNat = t + 1 := by
    simp only [BitVec.toNat_add, hivN, BitVec.toNat_ofNat]
    omega
  have hshbN : (BitVec.ofNat 64 64 - shVal).toNat = 64 - shVal.toNat := shb_toNat shVal hsh
  have hbody : shiftBodyLowCT = seqAll
    [ .RArrLoad ⟨"cy", .TU64⟩ ⟨"rp", .TBytes (8 * NRS)⟩ "idx"
    , .RArrLoad ⟨"t", .TU64⟩ ⟨"up", .TBytes (8 * NUS)⟩ "idx"
    , .RScalarSetExpr "shb" (.SSub (.SLit 64) (.SVar "sh"))
    , .RScalarSetExpr "lo" (.SShl (.SVar "t") (.SVar "sh"))
    , .RScalarSetExpr "hi" (.SShr (.SVar "t") (.SVar "shb"))
    , .RScalarSetExpr "s" (.SAdd (.SVar "lo") (.SVar "cy"))
    , .RArrStore ⟨"rp", .TBytes (8 * NRS)⟩ "idx" ⟨"s", .TU64⟩
    , .RScalarSetExpr "idx1" (.SAdd (.SVar "idx") (.SLit 1))
    , .RArrStore ⟨"rp", .TBytes (8 * NRS)⟩ "idx1" ⟨"hi", .TU64⟩ ] := rfl
  -- step 1: cy := rp[idx]
  obtain ⟨e1, hs1, h1cy, hf1⟩ :=
    semScalar_arrLoad (dstN := "cy") (tw := .TBytes (8 * NRS)) (idxN := "idx")
      (shiftEnv_rp up shVal acc iv) (shiftEnv_idx up shVal acc iv)
  rw [hivN] at h1cy
  have h1rp := (hf1 "rp" (by decide)).trans (shiftEnv_rp up shVal acc iv)
  have h1up := (hf1 "up" (by decide)).trans (shiftEnv_up up shVal acc iv)
  have h1idx := (hf1 "idx" (by decide)).trans (shiftEnv_idx up shVal acc iv)
  have h1sh := (hf1 "sh" (by decide)).trans (shiftEnv_sh up shVal acc iv)
  -- step 2: t := up[idx]
  obtain ⟨e2, hs2, h2t, hf2⟩ :=
    semScalar_arrLoad (dstN := "t") (tw := .TBytes (8 * NUS)) (idxN := "idx") h1up h1idx
  rw [hivN] at h2t
  have h2rp := (hf2 "rp" (by decide)).trans h1rp
  have h2idx := (hf2 "idx" (by decide)).trans h1idx
  have h2sh := (hf2 "sh" (by decide)).trans h1sh
  have h2cy := (hf2 "cy" (by decide)).trans h1cy
  -- step 3: shb := 64 - sh
  obtain ⟨e3, hs3, h3shb, hf3⟩ := semScalar_setExpr_run (y := "shb")
    (lower_lit_sub_var 64 (envReadU64_of_bound h2sh) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h2sh] at h3shb
  have h3rp := (hf3 "rp" (nt_rp) (by decide)).trans h2rp
  have h3idx := (hf3 "idx" (nt_idx) (by decide)).trans h2idx
  have h3sh := (hf3 "sh" (nt_sh) (by decide)).trans h2sh
  have h3cy := (hf3 "cy" (nt_cy) (by decide)).trans h2cy
  have h3t := (hf3 "t" (nt_t) (by decide)).trans h2t
  -- step 4: lo := t << sh
  obtain ⟨e4, hs4, h4lo, hf4⟩ := semScalar_setExpr_run (y := "lo")
    (lower_shl_vv (envReadU64_of_bound h3t) (envReadU64_of_bound h3sh))
  simp only [SExpr.evalBV, envReader_of_bound h3t, envReader_of_bound h3sh] at h4lo
  have h4rp := (hf4 "rp" (nt_rp) (by decide)).trans h3rp
  have h4idx := (hf4 "idx" (nt_idx) (by decide)).trans h3idx
  have h4cy := (hf4 "cy" (nt_cy) (by decide)).trans h3cy
  have h4t := (hf4 "t" (nt_t) (by decide)).trans h3t
  have h4shb := (hf4 "shb" (nt_shb) (by decide)).trans h3shb
  -- step 5: hi := t >> shb
  obtain ⟨e5, hs5, h5hi, hf5⟩ := semScalar_setExpr_run (y := "hi")
    (lower_shr_vv (envReadU64_of_bound h4t) (envReadU64_of_bound h4shb))
  simp only [SExpr.evalBV, envReader_of_bound h4t, envReader_of_bound h4shb] at h5hi
  rw [hshbN] at h5hi
  have h5rp := (hf5 "rp" (nt_rp) (by decide)).trans h4rp
  have h5idx := (hf5 "idx" (nt_idx) (by decide)).trans h4idx
  have h5cy := (hf5 "cy" (nt_cy) (by decide)).trans h4cy
  have h5lo := (hf5 "lo" (nt_lo) (by decide)).trans h4lo
  -- step 6: s := lo + cy
  obtain ⟨e6, hs6, h6s, hf6⟩ := semScalar_setExpr_run (y := "s")
    (lower_add_vv (envReadU64_of_bound h5lo) (envReadU64_of_bound h5cy))
  simp only [SExpr.evalBV, envReader_of_bound h5lo, envReader_of_bound h5cy] at h6s
  have h6rp := (hf6 "rp" (nt_rp) (by decide)).trans h5rp
  have h6idx := (hf6 "idx" (nt_idx) (by decide)).trans h5idx
  have h6hi := (hf6 "hi" (nt_hi) (by decide)).trans h5hi
  -- step 7: rp[idx] := s
  obtain ⟨e7, hs7, h7rp, hf7⟩ :=
    semScalar_arrStore (fw := 8 * NRS) h6rp h6idx h6s
  rw [hivN] at h7rp
  have h7idx := (hf7 "idx" (by decide)).trans h6idx
  have h7hi := (hf7 "hi" (by decide)).trans h6hi
  -- step 8: idx1 := idx + 1
  obtain ⟨e8, hs8, h8idx1, hf8⟩ := semScalar_setExpr_run (y := "idx1")
    (lower_add_lit 1 (envReadU64_of_bound h7idx) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h7idx] at h8idx1
  have h8rp := (hf8 "rp" (nt_rp) (by decide)).trans h7rp
  have h8hi := (hf8 "hi" (nt_hi) (by decide)).trans h7hi
  -- step 9: rp[idx1] := hi
  obtain ⟨e9, hs9, h9rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NRS) h8rp h8idx1 h8hi
  rw [hiv1N] at h9rp
  refine ⟨e9, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8]
    exact hs9
  · rw [h9rp]
    simp only [shiftFoldStep, shiftLimb]
    rfl

/-! ## 5. Coverage -/

/-- The funnel body is covered straight-line `LowCT`: two dynamic array reads,
    four `srcClean` scalar assignments, two dynamic array writes. -/
theorem shiftBody_coveredS : IsCoveredS shiftBodyLowCT :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _
          ⟨(by decide : (64 : Nat) < 2 ^ 64), nt_sh⟩)
        (.rSeq (.rScalarSetExpr _ _
            ⟨nt_t, nt_sh⟩)
          (.rSeq (.rScalarSetExpr _ _
              ⟨nt_t, nt_shb⟩)
            (.rSeq (.rScalarSetExpr _ _
                ⟨nt_lo, nt_cy⟩)
              (.rSeq (.rArrStore _ _ _)
                (.rSeq (.rScalarSetExpr _ _
                    ⟨nt_idx,
                      (by decide : (1 : Nat) < 2 ^ 64)⟩)
                  (.rArrStore _ _ _))))))))

/-- The funnel body sits in the control-extended covered fragment. -/
theorem shiftBody_covered : IsCoveredSCtl shiftBodyLowCT := .ofStraight shiftBody_coveredS

/-! ## 6. The front-compiled body -/

/-- The front accepts the funnel body. -/
theorem shiftFrontOk :
    (frontLoopBodyJ (accCTy := .memref NRS) vmBody "rp" shiftBodyLowCT).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the funnel
    shift body. -/
def shiftUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NRS)) :=
  (frontLoopBodyJ (accCTy := .memref NRS) vmBody "rp" shiftBodyLowCT).get shiftFrontOk

/-- The equation `shiftRtProg_denote` takes as its hypothesis. -/
theorem shiftUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NRS) vmBody "rp" shiftBodyLowCT = some shiftUpdate :=
  (Option.some_get shiftFrontOk).symm

/-! ## 7. The outer-argument accessors -/

/-- The source-array argument (RSI). -/
abbrev upVar : Ctxt.Var Gouter AU := .there (.there .here)

/-- The scalar shift-amount argument (RCX). -/
abbrev shVar : Ctxt.Var Gouter r64 := .here

/-! ## 8. The machine-level fold and value theorems -/

/-- **The runtime-trip funnel-shift program denotes the word-model fold.** The
    compiled program's denotation at any valuation is `shiftFold` of the argument
    registers — the trip count read from `n`, the source array and shift amount
    threaded as invariants, the output array as the accumulator seed. No
    front-compilation hypothesis remains. -/
theorem shiftRtProg_fold (V : Ctxt.Valuation Gouter) (hsh : (shVar.lookup V).toNat ≤ 64) :
    shiftRtProgOpt.map (fun c => ComL.denote c V)
      = some (shiftFold (upVar.lookup V) (shVar.lookup V).toNat
          (shiftCount.lookup V).toNat (shiftInit.lookup V)) := by
  rw [shiftRtProg_denote (update := shiftUpdate) shiftUpdate_eq V]
  congr 1
  have h64 := (shiftCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NRS)
    (invCTys := [.memref NUS, .sword 64]) vmBody "rp" shiftBodyLowCT shiftBody_covered
    (.cons (upVar.lookup V) (.cons (shVar.lookup V) .nil))
    (fun arr tt => shiftFoldStep (upVar.lookup V) (shVar.lookup V).toNat arr tt)
    (shiftCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        shiftLimbBody_run (upVar.lookup V) (shVar.lookup V) arr tt hsh (by omega)
      exact ⟨shiftEnv (upVar.lookup V) (shVar.lookup V) arr (BitVec.ofNat 64 tt), env',
        consistentS_shiftEnv (upVar.lookup V) (shVar.lookup V) arr (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    shiftUpdate_eq (shiftInit.lookup V)

/-- **The compiled funnel shift computes the scaled value.** For a trip count
    within the model's output array and a spill-in below `2 ^ sh`, the compiled
    program's output cells `0, …, n` recombine via `bignumVal` to
    `up[0..n) · 2^sh + rp[0]` — the model-level `shiftFold_val`, read on the
    machine-level denotation through the seam. -/
theorem shiftRtProg_val (V : Ctxt.Valuation Gouter)
    (hsh : (shVar.lookup V).toNat ≤ 64)
    (hn : (shiftCount.lookup V).toNat < NRS)
    (h0 : (memGetDyn (shiftInit.lookup V) 0).toNat < 2 ^ (shVar.lookup V).toNat) :
    ∃ out : Fin NRS → BitVec 64,
      shiftRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        bignumVal (cells out ((shiftCount.lookup V).toNat + 1))
          = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat)
              * 2 ^ (shVar.lookup V).toNat + (memGetDyn (shiftInit.lookup V) 0).toNat :=
  ⟨_, shiftRtProg_fold V hsh,
    shiftFold_val (upVar.lookup V) (shVar.lookup V).toNat hsh (shiftInit.lookup V) h0
      (shiftCount.lookup V).toNat hn⟩

/-- **The compiled `mpn_lshift` reading.** With `sh = cnt` and cell `0` seeded to
    zero, the output cells `0, …, n` are the shifted limbs and cell `n` the word
    shifted off the top — `lshiftFold_val` on the machine-level denotation. -/
theorem lshiftRtProg_val (V : Ctxt.Valuation Gouter)
    (hcnt : (shVar.lookup V).toNat ≤ 64)
    (hn : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0) :
    ∃ out : Fin NRS → BitVec 64,
      shiftRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        bignumVal (cells out ((shiftCount.lookup V).toNat + 1))
          = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat)
              * 2 ^ (shVar.lookup V).toNat :=
  ⟨_, shiftRtProg_fold V hcnt,
    lshiftFold_val (upVar.lookup V) (shVar.lookup V).toNat hcnt (shiftInit.lookup V) h0
      (shiftCount.lookup V).toNat hn⟩

/-- **The compiled `mpn_rshift` reading.** With `sh = 64 - cnt` and cell `0`
    seeded to zero, `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64` —
    `rshiftFold_val` on the machine-level denotation, for a `cnt ≤ 64`. -/
theorem rshiftRtProg_val (V : Ctxt.Valuation Gouter) (cnt : Nat) (hcnt : cnt ≤ 64)
    (hsheq : (shVar.lookup V).toNat = 64 - cnt)
    (hn : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0) :
    ∃ out : Fin NRS → BitVec 64,
      shiftRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        bignumVal (cells out ((shiftCount.lookup V).toNat + 1)) * 2 ^ cnt
          = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat) * 2 ^ 64 := by
  refine ⟨_, shiftRtProg_fold V (by omega), ?_⟩
  rw [hsheq]
  exact rshiftFold_val (upVar.lookup V) cnt hcnt (shiftInit.lookup V) h0
    (shiftCount.lookup V).toNat hn

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote
