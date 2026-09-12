/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The `mpn_addmul_1` and `mpn_submul_1` loop bodies against their source semantics

`MpnAddmulSubmul1FrontEmit.addmulRtProg_denote` / `submulRtProg_denote` state the
emitted runtime-trip loops' denotation as the `JLoopBodyN` fold of `update`,
under the hypothesis `frontLoopBodyJ … = some update`. This module supplies that
`update`, runs each source `LowCT` limb body symbolically through `semScalar`
from the canonical per-trip entry state, and identifies each trip with the
word-model step `accStep addmulLimb` / `accStep submulLimb` — so the model-level
value theorems `addmulFold_val_zero` / `submulFold_val_zero` read on the compiled
programs' denotations.

The per-trip run is the finite per-command check: three `RArrLoad`s (the carry
cell, the accumulator limb, the multiplicand limb), eleven `RScalarSetExpr`s and
two `RArrStore`s, each stepped by the waist lemmas of
`Secp256k1PointOpFrameRoundTrip`. The word identities it reuses are `hiU_eq` (the
`SMulHiU` evaluator is `mulHiW`) and `ltu_chain` (the emitted xor/and carry idiom
is `bSltu`), both from `MpnMul1FrontDenote`.

## Main results

* `addmulBody_covered` / `submulBody_covered` — the bodies are covered
  straight-line `LowCT`.
* `addmulLimbBody_run` / `submulLimbBody_run` — the per-trip `semScalar` run:
  from the canonical entry state at trip `t`, the body leaves the word-model
  step's array in `rp`.
* `addmulRtProg_fold` / `submulRtProg_fold` — each runtime-trip program's
  denotation is the `accFold` word-model fold, with no remaining hypothesis.
* `addmulRtProg_val` / `submulRtProg_val` — the machine-level value theorems: the
  compiled programs' output cells recombine via `bignumVal` to the multiply-
  accumulate / multiply-subtract contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontDenote

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
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
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (NU NR r64 AR AU Gouter ones sv seqAll rpLoc upLoc cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step lower_mul_vv lower_hiu_vv lower_add_vv lower_cq
   lower_cr lower_orshr hiU_eq ltu_chain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once — the `by decide` on
the below-`4` name length is paid a single time per name — and referenced at the
freshness sites below, instead of re-deciding the string length at each site. -/

theorem nt_c : ¬ isTmpName "c" := notTmp_of_short _ (by decide)
theorem nt_cq : ¬ isTmpName "cq" := notTmp_of_short _ (by decide)
theorem nt_cr : ¬ isTmpName "cr" := notTmp_of_short _ (by decide)
theorem nt_cy : ¬ isTmpName "cy" := notTmp_of_short _ (by decide)
theorem nt_d : ¬ isTmpName "d" := notTmp_of_short _ (by decide)
theorem nt_dq : ¬ isTmpName "dq" := notTmp_of_short _ (by decide)
theorem nt_dr : ¬ isTmpName "dr" := notTmp_of_short _ (by decide)
theorem nt_hi : ¬ isTmpName "hi" := notTmp_of_short _ (by decide)
theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_lo : ¬ isTmpName "lo" := notTmp_of_short _ (by decide)
theorem nt_o : ¬ isTmpName "o" := notTmp_of_short _ (by decide)
theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
theorem nt_s : ¬ isTmpName "s" := notTmp_of_short _ (by decide)
theorem nt_t : ¬ isTmpName "t" := notTmp_of_short _ (by decide)
theorem nt_u : ¬ isTmpName "u" := notTmp_of_short _ (by decide)
theorem nt_v : ¬ isTmpName "v" := notTmp_of_short _ (by decide)

/-! ## 1. New `SExpr`-lowering progress lemmas -/

/-- Progress of the nested word-add the carry-out fold `cyo = (hi + c) + d`
    lowers to. -/
theorem lower_add2 {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hzl : z.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SAdd (.SVar x) (.SVar y)) (.SVar z))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hzl 0), hz, envReadU64_upd_self]
  rfl

/-- Progress of the word-subtract `mpn_submul_1`'s accumulator step lowers to. -/
theorem lower_sub_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SSub (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- The loop-count index slot `nlimbs` is outside the reserved `__sx` temp
    namespace. -/
theorem notTmp_nlimbs : ¬ isTmpName "nlimbs" := by
  rintro ⟨k, hk⟩
  have hd := congrArg String.toList hk
  rw [tmpName, String.toList_append,
    show "nlimbs".toList = ['n', 'l', 'i', 'm', 'b', 's'] from rfl,
    show "__sx".toList = ['_', '_', 's', 'x'] from rfl] at hd
  simp only [List.cons_append, List.nil_append] at hd
  injection hd with h1 _
  exact absurd h1 (by decide)

/-! ## 2. The canonical per-trip entry state

Both bodies share the loop-body context `Gbody` and `vmBody`, so they share one
entry environment: the output array at `rp`, the trip index at `idx`, the
multiplicand array at `up`, the limb count / carry-cell index at `nlimbs`, the
scalar at `v`. -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of a multiply-accumulate limb body at one
    trip. -/
def mulaccEnv (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) : SEnvScalar :=
  (((((emptyEnv.upd "v" (t := .sword 64) b).upd
      "nlimbs" (t := .sword 64) nv).upd
      "up" (t := .memref NU) up).upd
      "idx" (t := .sword 64) iv).upd "rp" (t := .memref NR) acc)

theorem consistentS_mulaccEnv (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons up (.cons nv (.cons b .nil)))))
      (mulaccEnv up b nv acc iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind consistentS_empty "v" (t := .sword 64) b)
    "nlimbs" (t := .sword 64) nv) "up" (t := .memref NU) up)
    "idx" (t := .sword 64) iv) "rp" (t := .memref NR) acc

theorem mulaccEnv_rp (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mulaccEnv up b nv acc iv "rp" = some ⟨.memref NR, acc⟩ := upd_self _ _ _

theorem mulaccEnv_idx (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mulaccEnv up b nv acc iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [mulaccEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem mulaccEnv_up (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mulaccEnv up b nv acc iv "up" = some ⟨.memref NU, up⟩ := by
  rw [mulaccEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem mulaccEnv_nlimbs (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mulaccEnv up b nv acc iv "nlimbs" = some ⟨.sword 64, nv⟩ := by
  rw [mulaccEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

theorem mulaccEnv_v (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mulaccEnv up b nv acc iv "v" = some ⟨.sword 64, b⟩ := by
  rw [mulaccEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide),
    upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 3. Coverage -/

/-- Literal bound for the all-ones mask. -/
theorem hones : ones < 2 ^ 64 := by decide

/-- The `mpn_addmul_1` limb body is covered straight-line `LowCT`. -/
theorem addmulBody_coveredS : IsCoveredS addmulBodyLowCT :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rArrLoad _ _ _)
        (.rSeq (.rScalarSetExpr _ _
            ⟨nt_t, nt_v⟩)
          (.rSeq (.rScalarSetExpr _ _
              ⟨nt_t, nt_v⟩)
            (.rSeq (.rScalarSetExpr _ _
                ⟨nt_lo, nt_cy⟩)
              (.rSeq (.rScalarSetExpr _ _
                  ⟨⟨nt_s, hones⟩,
                    nt_lo⟩)
                (.rSeq (.rScalarSetExpr _ _
                    ⟨⟨⟨nt_s, nt_lo⟩,
                        hones⟩,
                      ⟨nt_s, nt_lo⟩⟩)
                  (.rSeq (.rScalarSetExpr _ _
                      ⟨⟨⟨nt_cq, nt_cr⟩,
                          ⟨nt_cq, nt_cr⟩⟩,
                        (by decide : (63 : Nat) < 2 ^ 64)⟩)
                    (.rSeq (.rScalarSetExpr _ _
                        ⟨nt_s, nt_o⟩)
                      (.rSeq (.rScalarSetExpr _ _
                          ⟨⟨nt_u, hones⟩,
                            nt_s⟩)
                        (.rSeq (.rScalarSetExpr _ _
                            ⟨⟨⟨nt_u, nt_s⟩,
                                hones⟩,
                              ⟨nt_u, nt_s⟩⟩)
                          (.rSeq (.rScalarSetExpr _ _
                              ⟨⟨⟨nt_dq, nt_dr⟩,
                                  ⟨nt_dq, nt_dr⟩⟩,
                                (by decide : (63 : Nat) < 2 ^ 64)⟩)
                            (.rSeq (.rScalarSetExpr _ _
                                ⟨⟨nt_hi, nt_c⟩,
                                  nt_d⟩)
                              (.rSeq (.rArrStore _ _ _)
                                (.rArrStore _ _ _)))))))))))))))

/-- The `mpn_addmul_1` limb body sits in the control-extended covered fragment. -/
theorem addmulBody_covered : IsCoveredSCtl addmulBodyLowCT :=
  .ofStraight addmulBody_coveredS

/-- The `mpn_submul_1` limb body is covered straight-line `LowCT`. -/
theorem submulBody_coveredS : IsCoveredS submulBodyLowCT :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rArrLoad _ _ _)
        (.rSeq (.rScalarSetExpr _ _
            ⟨nt_t, nt_v⟩)
          (.rSeq (.rScalarSetExpr _ _
              ⟨nt_t, nt_v⟩)
            (.rSeq (.rScalarSetExpr _ _
                ⟨nt_lo, nt_cy⟩)
              (.rSeq (.rScalarSetExpr _ _
                  ⟨⟨nt_s, hones⟩,
                    nt_lo⟩)
                (.rSeq (.rScalarSetExpr _ _
                    ⟨⟨⟨nt_s, nt_lo⟩,
                        hones⟩,
                      ⟨nt_s, nt_lo⟩⟩)
                  (.rSeq (.rScalarSetExpr _ _
                      ⟨⟨⟨nt_cq, nt_cr⟩,
                          ⟨nt_cq, nt_cr⟩⟩,
                        (by decide : (63 : Nat) < 2 ^ 64)⟩)
                    (.rSeq (.rScalarSetExpr _ _
                        ⟨nt_o, nt_s⟩)
                      (.rSeq (.rScalarSetExpr _ _
                          ⟨⟨nt_o, hones⟩,
                            nt_s⟩)
                        (.rSeq (.rScalarSetExpr _ _
                            ⟨⟨⟨nt_o, nt_s⟩,
                                hones⟩,
                              ⟨nt_o, nt_s⟩⟩)
                          (.rSeq (.rScalarSetExpr _ _
                              ⟨⟨⟨nt_dq, nt_dr⟩,
                                  ⟨nt_dq, nt_dr⟩⟩,
                                (by decide : (63 : Nat) < 2 ^ 64)⟩)
                            (.rSeq (.rScalarSetExpr _ _
                                ⟨⟨nt_hi, nt_c⟩,
                                  nt_d⟩)
                              (.rSeq (.rArrStore _ _ _)
                                (.rArrStore _ _ _)))))))))))))))

/-- The `mpn_submul_1` limb body sits in the control-extended covered fragment. -/
theorem submulBody_covered : IsCoveredSCtl submulBodyLowCT :=
  .ofStraight submulBody_coveredS

/-! ## 4. The per-trip runs -/

/-- **The `mpn_addmul_1` limb body computes one `accStep addmulLimb`.** From the
    canonical entry state at trip `t`, the source body's `semScalar` run
    terminates and leaves the word-model step's array in `rp`: the multiply-add
    low word at cell `t` and the carry-out at the carry cell `nlimbs`. -/
theorem addmulLimbBody_run (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar addmulBodyLowCT (mulaccEnv up b nv acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NR, accStep addmulLimb up b nv.toNat acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by simp only [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : addmulBodyLowCT = seqAll
    [ .RArrLoad ⟨"cy", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "nlimbs"
    , .RArrLoad ⟨"o", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "idx"
    , .RArrLoad ⟨"t", .TU64⟩ ⟨"up", .TBytes (8 * NU)⟩ "idx"
    , .RScalarSetExpr "lo" (.SMul (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "hi" (.SMulHiU (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "s" (.SAdd (.SVar "lo") (.SVar "cy"))
    , .RScalarSetExpr "cq" (.SAnd (.SXor (.SVar "s") (.SLit ones)) (.SVar "lo"))
    , .RScalarSetExpr "cr" (.SAnd (.SXor (.SXor (.SVar "s") (.SVar "lo")) (.SLit ones))
        (.SSub (.SVar "s") (.SVar "lo")))
    , .RScalarSetExpr "c" (.SShr (.SXor (.SXor (.SVar "cq") (.SVar "cr"))
        (.SAnd (.SVar "cq") (.SVar "cr"))) (.SLit 63))
    , .RScalarSetExpr "u" (.SAdd (.SVar "s") (.SVar "o"))
    , .RScalarSetExpr "dq" (.SAnd (.SXor (.SVar "u") (.SLit ones)) (.SVar "s"))
    , .RScalarSetExpr "dr" (.SAnd (.SXor (.SXor (.SVar "u") (.SVar "s")) (.SLit ones))
        (.SSub (.SVar "u") (.SVar "s")))
    , .RScalarSetExpr "d" (.SShr (.SXor (.SXor (.SVar "dq") (.SVar "dr"))
        (.SAnd (.SVar "dq") (.SVar "dr"))) (.SLit 63))
    , .RScalarSetExpr "cyo" (.SAdd (.SAdd (.SVar "hi") (.SVar "c")) (.SVar "d"))
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "idx" ⟨"u", .TU64⟩
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "nlimbs" ⟨"cyo", .TU64⟩ ] := rfl
  -- step 1: cy := rp[nlimbs]
  obtain ⟨e1, hs1, h1cy, hf1⟩ :=
    semScalar_arrLoad (dstN := "cy") (tw := .TBytes (8 * NR)) (idxN := "nlimbs")
      (mulaccEnv_rp up b nv acc iv) (mulaccEnv_nlimbs up b nv acc iv)
  have h1rp := (hf1 "rp" (by decide)).trans (mulaccEnv_rp up b nv acc iv)
  have h1up := (hf1 "up" (by decide)).trans (mulaccEnv_up up b nv acc iv)
  have h1idx := (hf1 "idx" (by decide)).trans (mulaccEnv_idx up b nv acc iv)
  have h1nlimbs := (hf1 "nlimbs" (by decide)).trans (mulaccEnv_nlimbs up b nv acc iv)
  have h1v := (hf1 "v" (by decide)).trans (mulaccEnv_v up b nv acc iv)
  -- step 2: o := rp[idx]
  obtain ⟨e2, hs2, h2o, hf2⟩ :=
    semScalar_arrLoad (dstN := "o") (tw := .TBytes (8 * NR)) (idxN := "idx") h1rp h1idx
  rw [hivN] at h2o
  have h2rp := (hf2 "rp" (by decide)).trans h1rp
  have h2up := (hf2 "up" (by decide)).trans h1up
  have h2idx := (hf2 "idx" (by decide)).trans h1idx
  have h2nlimbs := (hf2 "nlimbs" (by decide)).trans h1nlimbs
  have h2v := (hf2 "v" (by decide)).trans h1v
  have h2cy := (hf2 "cy" (by decide)).trans h1cy
  -- step 3: t := up[idx]
  obtain ⟨e3, hs3, h3t, hf3⟩ :=
    semScalar_arrLoad (dstN := "t") (tw := .TBytes (8 * NU)) (idxN := "idx") h2up h2idx
  rw [hivN] at h3t
  have h3rp := (hf3 "rp" (by decide)).trans h2rp
  have h3idx := (hf3 "idx" (by decide)).trans h2idx
  have h3nlimbs := (hf3 "nlimbs" (by decide)).trans h2nlimbs
  have h3v := (hf3 "v" (by decide)).trans h2v
  have h3cy := (hf3 "cy" (by decide)).trans h2cy
  have h3o := (hf3 "o" (by decide)).trans h2o
  -- step 4: lo := t * v
  obtain ⟨e4, hs4, h4lo, hf4⟩ := semScalar_setExpr_run (y := "lo")
    (lower_mul_vv (envReadU64_of_bound h3t) (envReadU64_of_bound h3v))
  simp only [SExpr.evalBV, envReader_of_bound h3t, envReader_of_bound h3v] at h4lo
  have h4rp := (hf4 "rp" (nt_rp) (by decide)).trans h3rp
  have h4idx := (hf4 "idx" (nt_idx) (by decide)).trans h3idx
  have h4nlimbs := (hf4 "nlimbs" notTmp_nlimbs (by decide)).trans h3nlimbs
  have h4v := (hf4 "v" (nt_v) (by decide)).trans h3v
  have h4cy := (hf4 "cy" (nt_cy) (by decide)).trans h3cy
  have h4o := (hf4 "o" (nt_o) (by decide)).trans h3o
  have h4t := (hf4 "t" (nt_t) (by decide)).trans h3t
  -- step 5: hi := mulhi(t, v)
  obtain ⟨e5, hs5, h5hi, hf5⟩ := semScalar_setExpr_run (y := "hi")
    (lower_hiu_vv (envReadU64_of_bound h4t) (envReadU64_of_bound h4v))
  simp only [SExpr.evalBV, envReader_of_bound h4t, envReader_of_bound h4v, hiU_eq] at h5hi
  have h5rp := (hf5 "rp" (nt_rp) (by decide)).trans h4rp
  have h5idx := (hf5 "idx" (nt_idx) (by decide)).trans h4idx
  have h5nlimbs := (hf5 "nlimbs" notTmp_nlimbs (by decide)).trans h4nlimbs
  have h5cy := (hf5 "cy" (nt_cy) (by decide)).trans h4cy
  have h5o := (hf5 "o" (nt_o) (by decide)).trans h4o
  have h5lo := (hf5 "lo" (nt_lo) (by decide)).trans h4lo
  -- step 6: s := lo + cy
  obtain ⟨e6, hs6, h6s, hf6⟩ := semScalar_setExpr_run (y := "s")
    (lower_add_vv (envReadU64_of_bound h5lo) (envReadU64_of_bound h5cy))
  simp only [SExpr.evalBV, envReader_of_bound h5lo, envReader_of_bound h5cy] at h6s
  have h6rp := (hf6 "rp" (nt_rp) (by decide)).trans h5rp
  have h6idx := (hf6 "idx" (nt_idx) (by decide)).trans h5idx
  have h6nlimbs := (hf6 "nlimbs" notTmp_nlimbs (by decide)).trans h5nlimbs
  have h6o := (hf6 "o" (nt_o) (by decide)).trans h5o
  have h6lo := (hf6 "lo" (nt_lo) (by decide)).trans h5lo
  have h6hi := (hf6 "hi" (nt_hi) (by decide)).trans h5hi
  -- step 7: cq := (~s) & lo
  obtain ⟨e7, hs7, h7cq, hf7⟩ := semScalar_setExpr_run (y := "cq")
    (lower_cq ones (envReadU64_of_bound h6s) (envReadU64_of_bound h6lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h6s, envReader_of_bound h6lo] at h7cq
  have h7rp := (hf7 "rp" (nt_rp) (by decide)).trans h6rp
  have h7idx := (hf7 "idx" (nt_idx) (by decide)).trans h6idx
  have h7nlimbs := (hf7 "nlimbs" notTmp_nlimbs (by decide)).trans h6nlimbs
  have h7o := (hf7 "o" (nt_o) (by decide)).trans h6o
  have h7lo := (hf7 "lo" (nt_lo) (by decide)).trans h6lo
  have h7hi := (hf7 "hi" (nt_hi) (by decide)).trans h6hi
  have h7s := (hf7 "s" (nt_s) (by decide)).trans h6s
  -- step 8: cr := (~(s ^ lo)) & (s - lo)
  obtain ⟨e8, hs8, h8cr, hf8⟩ := semScalar_setExpr_run (y := "cr")
    (lower_cr ones (envReadU64_of_bound h7s) (envReadU64_of_bound h7lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h7s, envReader_of_bound h7lo] at h8cr
  have h8rp := (hf8 "rp" (nt_rp) (by decide)).trans h7rp
  have h8idx := (hf8 "idx" (nt_idx) (by decide)).trans h7idx
  have h8nlimbs := (hf8 "nlimbs" notTmp_nlimbs (by decide)).trans h7nlimbs
  have h8o := (hf8 "o" (nt_o) (by decide)).trans h7o
  have h8hi := (hf8 "hi" (nt_hi) (by decide)).trans h7hi
  have h8s := (hf8 "s" (nt_s) (by decide)).trans h7s
  have h8cq := (hf8 "cq" (nt_cq) (by decide)).trans h7cq
  -- step 9: c := ((cq | cr) >> 63)
  obtain ⟨e9, hs9, h9c, hf9⟩ := semScalar_setExpr_run (y := "c")
    (lower_orshr 63 (envReadU64_of_bound h8cq) (envReadU64_of_bound h8cr)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h8cq, envReader_of_bound h8cr] at h9c
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h9c
  have h9rp := (hf9 "rp" (nt_rp) (by decide)).trans h8rp
  have h9idx := (hf9 "idx" (nt_idx) (by decide)).trans h8idx
  have h9nlimbs := (hf9 "nlimbs" notTmp_nlimbs (by decide)).trans h8nlimbs
  have h9o := (hf9 "o" (nt_o) (by decide)).trans h8o
  have h9hi := (hf9 "hi" (nt_hi) (by decide)).trans h8hi
  have h9s := (hf9 "s" (nt_s) (by decide)).trans h8s
  -- step 10: u := s + o
  obtain ⟨e10, hs10, h10u, hf10⟩ := semScalar_setExpr_run (y := "u")
    (lower_add_vv (envReadU64_of_bound h9s) (envReadU64_of_bound h9o))
  simp only [SExpr.evalBV, envReader_of_bound h9s, envReader_of_bound h9o] at h10u
  have h10rp := (hf10 "rp" (nt_rp) (by decide)).trans h9rp
  have h10idx := (hf10 "idx" (nt_idx) (by decide)).trans h9idx
  have h10nlimbs := (hf10 "nlimbs" notTmp_nlimbs (by decide)).trans h9nlimbs
  have h10hi := (hf10 "hi" (nt_hi) (by decide)).trans h9hi
  have h10s := (hf10 "s" (nt_s) (by decide)).trans h9s
  have h10c := (hf10 "c" (nt_c) (by decide)).trans h9c
  -- step 11: dq := (~u) & s
  obtain ⟨e11, hs11, h11dq, hf11⟩ := semScalar_setExpr_run (y := "dq")
    (lower_cq ones (envReadU64_of_bound h10u) (envReadU64_of_bound h10s)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h10u, envReader_of_bound h10s] at h11dq
  have h11rp := (hf11 "rp" (nt_rp) (by decide)).trans h10rp
  have h11idx := (hf11 "idx" (nt_idx) (by decide)).trans h10idx
  have h11nlimbs := (hf11 "nlimbs" notTmp_nlimbs (by decide)).trans h10nlimbs
  have h11hi := (hf11 "hi" (nt_hi) (by decide)).trans h10hi
  have h11s := (hf11 "s" (nt_s) (by decide)).trans h10s
  have h11c := (hf11 "c" (nt_c) (by decide)).trans h10c
  have h11u := (hf11 "u" (nt_u) (by decide)).trans h10u
  -- step 12: dr := (~(u ^ s)) & (u - s)
  obtain ⟨e12, hs12, h12dr, hf12⟩ := semScalar_setExpr_run (y := "dr")
    (lower_cr ones (envReadU64_of_bound h11u) (envReadU64_of_bound h11s)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h11u, envReader_of_bound h11s] at h12dr
  have h12rp := (hf12 "rp" (nt_rp) (by decide)).trans h11rp
  have h12idx := (hf12 "idx" (nt_idx) (by decide)).trans h11idx
  have h12nlimbs := (hf12 "nlimbs" notTmp_nlimbs (by decide)).trans h11nlimbs
  have h12hi := (hf12 "hi" (nt_hi) (by decide)).trans h11hi
  have h12c := (hf12 "c" (nt_c) (by decide)).trans h11c
  have h12u := (hf12 "u" (nt_u) (by decide)).trans h11u
  have h12dq := (hf12 "dq" (nt_dq) (by decide)).trans h11dq
  -- step 13: d := ((dq | dr) >> 63)
  obtain ⟨e13, hs13, h13d, hf13⟩ := semScalar_setExpr_run (y := "d")
    (lower_orshr 63 (envReadU64_of_bound h12dq) (envReadU64_of_bound h12dr)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h12dq, envReader_of_bound h12dr] at h13d
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h13d
  have h13rp := (hf13 "rp" (nt_rp) (by decide)).trans h12rp
  have h13idx := (hf13 "idx" (nt_idx) (by decide)).trans h12idx
  have h13nlimbs := (hf13 "nlimbs" notTmp_nlimbs (by decide)).trans h12nlimbs
  have h13hi := (hf13 "hi" (nt_hi) (by decide)).trans h12hi
  have h13c := (hf13 "c" (nt_c) (by decide)).trans h12c
  have h13u := (hf13 "u" (nt_u) (by decide)).trans h12u
  -- step 14: cyo := (hi + c) + d
  obtain ⟨e14, hs14, h14cyo, hf14⟩ := semScalar_setExpr_run (y := "cyo")
    (lower_add2 (envReadU64_of_bound h13hi) (envReadU64_of_bound h13c)
      (envReadU64_of_bound h13d) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h13hi, envReader_of_bound h13c,
    envReader_of_bound h13d] at h14cyo
  have h14rp := (hf14 "rp" (nt_rp) (by decide)).trans h13rp
  have h14idx := (hf14 "idx" (nt_idx) (by decide)).trans h13idx
  have h14nlimbs := (hf14 "nlimbs" notTmp_nlimbs (by decide)).trans h13nlimbs
  have h14u := (hf14 "u" (nt_u) (by decide)).trans h13u
  -- step 15: rp[idx] := u
  obtain ⟨e15, hs15, h15rp, hf15⟩ :=
    semScalar_arrStore (fw := 8 * NR) h14rp h14idx h14u
  rw [hivN] at h15rp
  have h15nlimbs := (hf15 "nlimbs" (by decide)).trans h14nlimbs
  have h15cyo := (hf15 "cyo" (by decide)).trans h14cyo
  -- step 16: rp[nlimbs] := cyo
  obtain ⟨e16, hs16, h16rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h15rp h15nlimbs h15cyo
  refine ⟨e16, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8,
      seqAll_step hs9, seqAll_step hs10, seqAll_step hs11, seqAll_step hs12,
      seqAll_step hs13, seqAll_step hs14, seqAll_step hs15]
    exact hs16
  · rw [h16rp]
    simp only [accStep, addmulLimb]
    rfl

/-- **The `mpn_submul_1` limb body computes one `accStep submulLimb`.** From the
    canonical entry state at trip `t`, the source body's `semScalar` run
    terminates and leaves the word-model step's array in `rp`: the multiply-
    subtract low word at cell `t` and the borrow-carry at the carry cell
    `nlimbs`. -/
theorem submulLimbBody_run (up : Fin NU → BitVec 64) (b nv : BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar submulBodyLowCT (mulaccEnv up b nv acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NR, accStep submulLimb up b nv.toNat acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by simp only [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : submulBodyLowCT = seqAll
    [ .RArrLoad ⟨"cy", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "nlimbs"
    , .RArrLoad ⟨"o", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "idx"
    , .RArrLoad ⟨"t", .TU64⟩ ⟨"up", .TBytes (8 * NU)⟩ "idx"
    , .RScalarSetExpr "lo" (.SMul (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "hi" (.SMulHiU (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "s" (.SAdd (.SVar "lo") (.SVar "cy"))
    , .RScalarSetExpr "cq" (.SAnd (.SXor (.SVar "s") (.SLit ones)) (.SVar "lo"))
    , .RScalarSetExpr "cr" (.SAnd (.SXor (.SXor (.SVar "s") (.SVar "lo")) (.SLit ones))
        (.SSub (.SVar "s") (.SVar "lo")))
    , .RScalarSetExpr "c" (.SShr (.SXor (.SXor (.SVar "cq") (.SVar "cr"))
        (.SAnd (.SVar "cq") (.SVar "cr"))) (.SLit 63))
    , .RScalarSetExpr "u" (.SSub (.SVar "o") (.SVar "s"))
    , .RScalarSetExpr "dq" (.SAnd (.SXor (.SVar "o") (.SLit ones)) (.SVar "s"))
    , .RScalarSetExpr "dr" (.SAnd (.SXor (.SXor (.SVar "o") (.SVar "s")) (.SLit ones))
        (.SSub (.SVar "o") (.SVar "s")))
    , .RScalarSetExpr "d" (.SShr (.SXor (.SXor (.SVar "dq") (.SVar "dr"))
        (.SAnd (.SVar "dq") (.SVar "dr"))) (.SLit 63))
    , .RScalarSetExpr "cyo" (.SAdd (.SAdd (.SVar "hi") (.SVar "c")) (.SVar "d"))
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "idx" ⟨"u", .TU64⟩
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "nlimbs" ⟨"cyo", .TU64⟩ ] := rfl
  -- step 1: cy := rp[nlimbs]
  obtain ⟨e1, hs1, h1cy, hf1⟩ :=
    semScalar_arrLoad (dstN := "cy") (tw := .TBytes (8 * NR)) (idxN := "nlimbs")
      (mulaccEnv_rp up b nv acc iv) (mulaccEnv_nlimbs up b nv acc iv)
  have h1rp := (hf1 "rp" (by decide)).trans (mulaccEnv_rp up b nv acc iv)
  have h1up := (hf1 "up" (by decide)).trans (mulaccEnv_up up b nv acc iv)
  have h1idx := (hf1 "idx" (by decide)).trans (mulaccEnv_idx up b nv acc iv)
  have h1nlimbs := (hf1 "nlimbs" (by decide)).trans (mulaccEnv_nlimbs up b nv acc iv)
  have h1v := (hf1 "v" (by decide)).trans (mulaccEnv_v up b nv acc iv)
  -- step 2: o := rp[idx]
  obtain ⟨e2, hs2, h2o, hf2⟩ :=
    semScalar_arrLoad (dstN := "o") (tw := .TBytes (8 * NR)) (idxN := "idx") h1rp h1idx
  rw [hivN] at h2o
  have h2rp := (hf2 "rp" (by decide)).trans h1rp
  have h2up := (hf2 "up" (by decide)).trans h1up
  have h2idx := (hf2 "idx" (by decide)).trans h1idx
  have h2nlimbs := (hf2 "nlimbs" (by decide)).trans h1nlimbs
  have h2v := (hf2 "v" (by decide)).trans h1v
  have h2cy := (hf2 "cy" (by decide)).trans h1cy
  -- step 3: t := up[idx]
  obtain ⟨e3, hs3, h3t, hf3⟩ :=
    semScalar_arrLoad (dstN := "t") (tw := .TBytes (8 * NU)) (idxN := "idx") h2up h2idx
  rw [hivN] at h3t
  have h3rp := (hf3 "rp" (by decide)).trans h2rp
  have h3idx := (hf3 "idx" (by decide)).trans h2idx
  have h3nlimbs := (hf3 "nlimbs" (by decide)).trans h2nlimbs
  have h3v := (hf3 "v" (by decide)).trans h2v
  have h3cy := (hf3 "cy" (by decide)).trans h2cy
  have h3o := (hf3 "o" (by decide)).trans h2o
  -- step 4: lo := t * v
  obtain ⟨e4, hs4, h4lo, hf4⟩ := semScalar_setExpr_run (y := "lo")
    (lower_mul_vv (envReadU64_of_bound h3t) (envReadU64_of_bound h3v))
  simp only [SExpr.evalBV, envReader_of_bound h3t, envReader_of_bound h3v] at h4lo
  have h4rp := (hf4 "rp" (nt_rp) (by decide)).trans h3rp
  have h4idx := (hf4 "idx" (nt_idx) (by decide)).trans h3idx
  have h4nlimbs := (hf4 "nlimbs" notTmp_nlimbs (by decide)).trans h3nlimbs
  have h4v := (hf4 "v" (nt_v) (by decide)).trans h3v
  have h4cy := (hf4 "cy" (nt_cy) (by decide)).trans h3cy
  have h4o := (hf4 "o" (nt_o) (by decide)).trans h3o
  have h4t := (hf4 "t" (nt_t) (by decide)).trans h3t
  -- step 5: hi := mulhi(t, v)
  obtain ⟨e5, hs5, h5hi, hf5⟩ := semScalar_setExpr_run (y := "hi")
    (lower_hiu_vv (envReadU64_of_bound h4t) (envReadU64_of_bound h4v))
  simp only [SExpr.evalBV, envReader_of_bound h4t, envReader_of_bound h4v, hiU_eq] at h5hi
  have h5rp := (hf5 "rp" (nt_rp) (by decide)).trans h4rp
  have h5idx := (hf5 "idx" (nt_idx) (by decide)).trans h4idx
  have h5nlimbs := (hf5 "nlimbs" notTmp_nlimbs (by decide)).trans h4nlimbs
  have h5cy := (hf5 "cy" (nt_cy) (by decide)).trans h4cy
  have h5o := (hf5 "o" (nt_o) (by decide)).trans h4o
  have h5lo := (hf5 "lo" (nt_lo) (by decide)).trans h4lo
  -- step 6: s := lo + cy
  obtain ⟨e6, hs6, h6s, hf6⟩ := semScalar_setExpr_run (y := "s")
    (lower_add_vv (envReadU64_of_bound h5lo) (envReadU64_of_bound h5cy))
  simp only [SExpr.evalBV, envReader_of_bound h5lo, envReader_of_bound h5cy] at h6s
  have h6rp := (hf6 "rp" (nt_rp) (by decide)).trans h5rp
  have h6idx := (hf6 "idx" (nt_idx) (by decide)).trans h5idx
  have h6nlimbs := (hf6 "nlimbs" notTmp_nlimbs (by decide)).trans h5nlimbs
  have h6o := (hf6 "o" (nt_o) (by decide)).trans h5o
  have h6lo := (hf6 "lo" (nt_lo) (by decide)).trans h5lo
  have h6hi := (hf6 "hi" (nt_hi) (by decide)).trans h5hi
  -- step 7: cq := (~s) & lo
  obtain ⟨e7, hs7, h7cq, hf7⟩ := semScalar_setExpr_run (y := "cq")
    (lower_cq ones (envReadU64_of_bound h6s) (envReadU64_of_bound h6lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h6s, envReader_of_bound h6lo] at h7cq
  have h7rp := (hf7 "rp" (nt_rp) (by decide)).trans h6rp
  have h7idx := (hf7 "idx" (nt_idx) (by decide)).trans h6idx
  have h7nlimbs := (hf7 "nlimbs" notTmp_nlimbs (by decide)).trans h6nlimbs
  have h7o := (hf7 "o" (nt_o) (by decide)).trans h6o
  have h7lo := (hf7 "lo" (nt_lo) (by decide)).trans h6lo
  have h7hi := (hf7 "hi" (nt_hi) (by decide)).trans h6hi
  have h7s := (hf7 "s" (nt_s) (by decide)).trans h6s
  -- step 8: cr := (~(s ^ lo)) & (s - lo)
  obtain ⟨e8, hs8, h8cr, hf8⟩ := semScalar_setExpr_run (y := "cr")
    (lower_cr ones (envReadU64_of_bound h7s) (envReadU64_of_bound h7lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h7s, envReader_of_bound h7lo] at h8cr
  have h8rp := (hf8 "rp" (nt_rp) (by decide)).trans h7rp
  have h8idx := (hf8 "idx" (nt_idx) (by decide)).trans h7idx
  have h8nlimbs := (hf8 "nlimbs" notTmp_nlimbs (by decide)).trans h7nlimbs
  have h8o := (hf8 "o" (nt_o) (by decide)).trans h7o
  have h8hi := (hf8 "hi" (nt_hi) (by decide)).trans h7hi
  have h8s := (hf8 "s" (nt_s) (by decide)).trans h7s
  have h8cq := (hf8 "cq" (nt_cq) (by decide)).trans h7cq
  -- step 9: c := ((cq | cr) >> 63)
  obtain ⟨e9, hs9, h9c, hf9⟩ := semScalar_setExpr_run (y := "c")
    (lower_orshr 63 (envReadU64_of_bound h8cq) (envReadU64_of_bound h8cr)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h8cq, envReader_of_bound h8cr] at h9c
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h9c
  have h9rp := (hf9 "rp" (nt_rp) (by decide)).trans h8rp
  have h9idx := (hf9 "idx" (nt_idx) (by decide)).trans h8idx
  have h9nlimbs := (hf9 "nlimbs" notTmp_nlimbs (by decide)).trans h8nlimbs
  have h9o := (hf9 "o" (nt_o) (by decide)).trans h8o
  have h9hi := (hf9 "hi" (nt_hi) (by decide)).trans h8hi
  have h9s := (hf9 "s" (nt_s) (by decide)).trans h8s
  -- step 10: u := o - s
  obtain ⟨e10, hs10, h10u, hf10⟩ := semScalar_setExpr_run (y := "u")
    (lower_sub_vv (envReadU64_of_bound h9o) (envReadU64_of_bound h9s))
  simp only [SExpr.evalBV, envReader_of_bound h9o, envReader_of_bound h9s] at h10u
  have h10rp := (hf10 "rp" (nt_rp) (by decide)).trans h9rp
  have h10idx := (hf10 "idx" (nt_idx) (by decide)).trans h9idx
  have h10nlimbs := (hf10 "nlimbs" notTmp_nlimbs (by decide)).trans h9nlimbs
  have h10hi := (hf10 "hi" (nt_hi) (by decide)).trans h9hi
  have h10s := (hf10 "s" (nt_s) (by decide)).trans h9s
  have h10c := (hf10 "c" (nt_c) (by decide)).trans h9c
  have h10o := (hf10 "o" (nt_o) (by decide)).trans h9o
  -- step 11: dq := (~o) & s
  obtain ⟨e11, hs11, h11dq, hf11⟩ := semScalar_setExpr_run (y := "dq")
    (lower_cq ones (envReadU64_of_bound h10o) (envReadU64_of_bound h10s)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h10o, envReader_of_bound h10s] at h11dq
  have h11rp := (hf11 "rp" (nt_rp) (by decide)).trans h10rp
  have h11idx := (hf11 "idx" (nt_idx) (by decide)).trans h10idx
  have h11nlimbs := (hf11 "nlimbs" notTmp_nlimbs (by decide)).trans h10nlimbs
  have h11hi := (hf11 "hi" (nt_hi) (by decide)).trans h10hi
  have h11s := (hf11 "s" (nt_s) (by decide)).trans h10s
  have h11c := (hf11 "c" (nt_c) (by decide)).trans h10c
  have h11o := (hf11 "o" (nt_o) (by decide)).trans h10o
  have h11u := (hf11 "u" (nt_u) (by decide)).trans h10u
  -- step 12: dr := (~(o ^ s)) & (o - s)
  obtain ⟨e12, hs12, h12dr, hf12⟩ := semScalar_setExpr_run (y := "dr")
    (lower_cr ones (envReadU64_of_bound h11o) (envReadU64_of_bound h11s)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h11o, envReader_of_bound h11s] at h12dr
  have h12rp := (hf12 "rp" (nt_rp) (by decide)).trans h11rp
  have h12idx := (hf12 "idx" (nt_idx) (by decide)).trans h11idx
  have h12nlimbs := (hf12 "nlimbs" notTmp_nlimbs (by decide)).trans h11nlimbs
  have h12hi := (hf12 "hi" (nt_hi) (by decide)).trans h11hi
  have h12c := (hf12 "c" (nt_c) (by decide)).trans h11c
  have h12u := (hf12 "u" (nt_u) (by decide)).trans h11u
  have h12dq := (hf12 "dq" (nt_dq) (by decide)).trans h11dq
  -- step 13: d := ((dq | dr) >> 63)
  obtain ⟨e13, hs13, h13d, hf13⟩ := semScalar_setExpr_run (y := "d")
    (lower_orshr 63 (envReadU64_of_bound h12dq) (envReadU64_of_bound h12dr)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h12dq, envReader_of_bound h12dr] at h13d
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h13d
  have h13rp := (hf13 "rp" (nt_rp) (by decide)).trans h12rp
  have h13idx := (hf13 "idx" (nt_idx) (by decide)).trans h12idx
  have h13nlimbs := (hf13 "nlimbs" notTmp_nlimbs (by decide)).trans h12nlimbs
  have h13hi := (hf13 "hi" (nt_hi) (by decide)).trans h12hi
  have h13c := (hf13 "c" (nt_c) (by decide)).trans h12c
  have h13u := (hf13 "u" (nt_u) (by decide)).trans h12u
  -- step 14: cyo := (hi + c) + d
  obtain ⟨e14, hs14, h14cyo, hf14⟩ := semScalar_setExpr_run (y := "cyo")
    (lower_add2 (envReadU64_of_bound h13hi) (envReadU64_of_bound h13c)
      (envReadU64_of_bound h13d) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h13hi, envReader_of_bound h13c,
    envReader_of_bound h13d] at h14cyo
  have h14rp := (hf14 "rp" (nt_rp) (by decide)).trans h13rp
  have h14idx := (hf14 "idx" (nt_idx) (by decide)).trans h13idx
  have h14nlimbs := (hf14 "nlimbs" notTmp_nlimbs (by decide)).trans h13nlimbs
  have h14u := (hf14 "u" (nt_u) (by decide)).trans h13u
  -- step 15: rp[idx] := u
  obtain ⟨e15, hs15, h15rp, hf15⟩ :=
    semScalar_arrStore (fw := 8 * NR) h14rp h14idx h14u
  rw [hivN] at h15rp
  have h15nlimbs := (hf15 "nlimbs" (by decide)).trans h14nlimbs
  have h15cyo := (hf15 "cyo" (by decide)).trans h14cyo
  -- step 16: rp[nlimbs] := cyo
  obtain ⟨e16, hs16, h16rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h15rp h15nlimbs h15cyo
  refine ⟨e16, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8,
      seqAll_step hs9, seqAll_step hs10, seqAll_step hs11, seqAll_step hs12,
      seqAll_step hs13, seqAll_step hs14, seqAll_step hs15]
    exact hs16
  · rw [h16rp]
    simp only [accStep, submulLimb]
    rfl

/-! ## 5. The front-compiled bodies -/

/-- The front accepts the `mpn_addmul_1` body. -/
theorem addmulFrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" addmulBodyLowCT).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_addmul_1` limb body. -/
def addmulUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" addmulBodyLowCT).get addmulFrontOk

/-- The equation `addmulRtProg_denote` takes as its hypothesis. -/
theorem addmulUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" addmulBodyLowCT = some addmulUpdate :=
  (Option.some_get addmulFrontOk).symm

/-- The front accepts the `mpn_submul_1` body. -/
theorem submulFrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" submulBodyLowCT).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_submul_1` limb body. -/
def submulUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" submulBodyLowCT).get submulFrontOk

/-- The equation `submulRtProg_denote` takes as its hypothesis. -/
theorem submulUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" submulBodyLowCT = some submulUpdate :=
  (Option.some_get submulFrontOk).symm

/-! ## 6. The machine-level fold and value theorems

The outer argument context is `Gouter = [v (RCX), n (RDX), up (RSI), rp (RDI)]`
(newest first). The carry cell is cell `n`, so the runtime trip count and the
carry-cell index coincide. -/

/-- The multiplicand-array argument (RSI). -/
abbrev upVarA : Ctxt.Var Gouter AU := .there (.there .here)

/-- The scalar-multiplier argument (RCX). -/
abbrev vVarA : Ctxt.Var Gouter r64 := .here

/-- **The runtime-trip `mpn_addmul_1` program denotes the word-model fold.** The
    compiled program's denotation at any valuation is `accFold addmulLimb` of the
    argument registers, with the carry cell and the trip count both the runtime
    `n`. No front-compilation hypothesis remains. -/
theorem addmulRtProg_fold (V : Ctxt.Valuation Gouter) :
    addmulRtProgOpt.map (fun c => ComL.denote c V)
      = some (accFold addmulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V)) := by
  rw [addmulRtProg_denote (update := addmulUpdate) addmulUpdate_eq V]
  congr 1
  have h64 := (accCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64]) vmBody "rp" addmulBodyLowCT
    addmulBody_covered
    (.cons (upVarA.lookup V) (.cons (accCount.lookup V) (.cons (vVarA.lookup V) .nil)))
    (fun arr tt => accStep addmulLimb (upVarA.lookup V) (vVarA.lookup V)
      (accCount.lookup V).toNat arr tt)
    (accCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        addmulLimbBody_run (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr tt
          (by omega)
      exact ⟨mulaccEnv (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr
          (BitVec.ofNat 64 tt), env',
        consistentS_mulaccEnv (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr
          (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    addmulUpdate_eq (accInit.lookup V)

/-- **The compiled `mpn_addmul_1` computes the multiply-accumulate.** For a trip
    count within the model's output array and a zeroed carry cell, the compiled
    program's output cells recombine via `bignumVal` to the multiply-accumulate
    contract — `addmulFold_val_zero` read on the machine-level denotation. -/
theorem addmulRtProg_val (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0) :
    ∃ out : Fin NR → BitVec 64,
      addmulRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
            + (2 ^ 64) ^ (accCount.lookup V).toNat
                * (memGetDyn out (accCount.lookup V).toNat).toNat
          = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
            + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                * (vVarA.lookup V).toNat :=
  ⟨_, addmulRtProg_fold V,
   addmulFold_val_zero (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V).toNat hn
     (accInit.lookup V) (accCount.lookup V).toNat (le_refl _) h0⟩

/-- **The runtime-trip `mpn_submul_1` program denotes the word-model fold.** The
    instance of the composition at the multiply-subtract kernel. -/
theorem submulRtProg_fold (V : Ctxt.Valuation Gouter) :
    submulRtProgOpt.map (fun c => ComL.denote c V)
      = some (accFold submulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V)) := by
  rw [submulRtProg_denote (update := submulUpdate) submulUpdate_eq V]
  congr 1
  have h64 := (accCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64]) vmBody "rp" submulBodyLowCT
    submulBody_covered
    (.cons (upVarA.lookup V) (.cons (accCount.lookup V) (.cons (vVarA.lookup V) .nil)))
    (fun arr tt => accStep submulLimb (upVarA.lookup V) (vVarA.lookup V)
      (accCount.lookup V).toNat arr tt)
    (accCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        submulLimbBody_run (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr tt
          (by omega)
      exact ⟨mulaccEnv (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr
          (BitVec.ofNat 64 tt), env',
        consistentS_mulaccEnv (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V) arr
          (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    submulUpdate_eq (accInit.lookup V)

/-- **The compiled `mpn_submul_1` computes the multiply-subtract.** For a trip
    count within the model's output array and a zeroed carry cell, the compiled
    program's output cells recombine via `bignumVal` to the multiply-subtract
    contract — `submulFold_val_zero` read on the machine-level denotation. -/
theorem submulRtProg_val (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0) :
    ∃ out : Fin NR → BitVec 64,
      submulRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
            + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                * (vVarA.lookup V).toNat
          = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
            + (2 ^ 64) ^ (accCount.lookup V).toNat
                * (memGetDyn out (accCount.lookup V).toNat).toNat :=
  ⟨_, submulRtProg_fold V,
   submulFold_val_zero (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V).toNat hn
     (accInit.lookup V) (accCount.lookup V).toNat (le_refl _) h0⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontDenote
