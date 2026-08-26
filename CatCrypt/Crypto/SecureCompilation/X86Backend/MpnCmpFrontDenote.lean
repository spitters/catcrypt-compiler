/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The `mpn_cmp` loop body against its source semantics

`MpnCmpFrontEmit.cmpRtProg_denote` states the emitted runtime-trip loop's
denotation as the `JLoopBodyN` fold of `update`, under the hypothesis
`frontLoopBodyJ … = some update`. This module supplies that `update` — using the
structural front-success gate `MpnCmpFrontTotal.cmpFrontOk` rather than a body
reduction — runs the source `LowCT` limb body symbolically through `semScalar`
from the canonical per-trip entry state, and identifies each trip with the
memref-carrier step `cmpFoldStep` — so the model-level value theorem
`cmpFold_val_full` reads on the compiled program's denotation.

The per-trip run is the finite per-command check: three index assignments, three
`RArrLoad`s (the two operand limbs and the running result), three `ltuCmds`
branch-free comparison blocks (two over the operand limbs, one for the
"result still zero" mask), the mask-select arithmetic, and one `RArrStore` back to
the result cell, each stepped by the waist lemmas of
`Secp256k1PointOpFrameRoundTrip`. The word identity it reuses is `ltu_chain` (the
emitted xor/and carry idiom is `bSltu`), from `MpnMul1FrontDenote`.

## Main results

* `cmpLimbBody_coveredS` / `cmpLimbBody_covered` — the limb body is covered
  straight-line `LowCT`.
* `cmpUpdate` / `cmpUpdate_eq` — the front-compiled limb body and the equation
  discharging `cmpRtProg_denote`'s hypothesis.
* `cmpLimbBody_run` — the per-trip `semScalar` run: from the canonical entry
  state at trip `t`, the body leaves `cmpFoldStep ap bp (n-1) acc t` in `rp`.
* `cmpRtProg_fold` — the runtime-trip program's denotation is the `cmpFold`
  memref-carrier fold, with no remaining hypothesis.
* `cmpRtProg_val` — the machine-level value theorem: the compiled program's
  result cell holds `cmpSign` of the two operands' `bignumVal`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote

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
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref (notTmp_of_headNe)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (ones seqAll)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step lower_cq lower_cr lower_orshr ltu_chain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal (cmpFrontOk)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once — the `by decide` on
the below-`4` name length is paid a single time per name — and referenced at the
freshness sites below, instead of re-deciding the string length at each site. -/

private theorem nt_ap : ¬ isTmpName "ap" := notTmp_of_short _ (by decide)
private theorem nt_bp : ¬ isTmpName "bp" := notTmp_of_short _ (by decide)
private theorem nt_dif : ¬ isTmpName "dif" := notTmp_of_short _ (by decide)
private theorem nt_gt : ¬ isTmpName "gt" := notTmp_of_short _ (by decide)
private theorem nt_gtq : ¬ isTmpName "gtq" := notTmp_of_short _ (by decide)
private theorem nt_gtr : ¬ isTmpName "gtr" := notTmp_of_short _ (by decide)
private theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
private theorem nt_j : ¬ isTmpName "j" := notTmp_of_short _ (by decide)
private theorem nt_lt : ¬ isTmpName "lt" := notTmp_of_short _ (by decide)
private theorem nt_ltq : ¬ isTmpName "ltq" := notTmp_of_short _ (by decide)
private theorem nt_ltr : ¬ isTmpName "ltr" := notTmp_of_short _ (by decide)
private theorem nt_n : ¬ isTmpName "n" := notTmp_of_short _ (by decide)
private theorem nt_nz : ¬ isTmpName "nz" := notTmp_of_short _ (by decide)
private theorem nt_nzq : ¬ isTmpName "nzq" := notTmp_of_short _ (by decide)
private theorem nt_nzr : ¬ isTmpName "nzr" := notTmp_of_short _ (by decide)
private theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
private theorem nt_top : ¬ isTmpName "top" := notTmp_of_short _ (by decide)
private theorem nt_x : ¬ isTmpName "x" := notTmp_of_short _ (by decide)
private theorem nt_y : ¬ isTmpName "y" := notTmp_of_short _ (by decide)
private theorem nt_z : ¬ isTmpName "z" := notTmp_of_short _ (by decide)

/-! ## 1. New `SExpr`-lowering progress lemmas -/

/-- A non-temp name misses the whole reserved `__sx` index range. -/
theorem ne_tmp_of_notTmp {y : String} (h : ¬ isTmpName y) (k : Nat) : y ≠ tmpName k :=
  fun hh => h ⟨k, hh⟩

/-- Progress of a bare literal. -/
theorem lower_lit {env : SEnvScalar} (L : Nat) : (semLowerSExpr env 0 (.SLit L)).isSome := rfl

/-- Progress of the word-subtract `dst - lit` index step. -/
theorem lower_sub_lit {env : SEnvScalar} {x : String} {wx : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SSub (.SVar x) (.SLit L))).isSome := by
  simp only [semLowerSExpr, hx, binNode, envReadU64_upd_ne (ne_tmp_of_short hxl 0),
    envReadU64_upd_self]
  rfl

/-- Progress of the word-subtract of two named slots. -/
theorem lower_sub_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SSub (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- Progress of the word-xor of two named slots. -/
theorem lower_xor_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SXor (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- Progress of the mask-select `x ^ (y & z)` the result update lowers to. -/
theorem lower_xor_and {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hxnt : ¬ isTmpName x) :
    (semLowerSExpr env 0 (.SXor (.SVar x) (.SAnd (.SVar y) (.SVar z)))).isSome := by
  simp only [semLowerSExpr, hx, hy, hz, binNode,
    envReadU64_upd_ne (ne_tmp_of_notTmp hxnt 0), envReadU64_upd_self]
  rfl

/-- Progress of the `(~0) & y` half of the `bSltu 0 y` mask block. -/
theorem lower_nzq {env : SEnvScalar} {y : String} {wy : BitVec 64}
    (hy : envReadU64 env y = some wy) (hynt : ¬ isTmpName y) :
    (semLowerSExpr env 0 (.SAnd (.SXor (.SLit 0) (.SLit ones)) (.SVar y))).isSome := by
  simp only [semLowerSExpr, binNode, hy, envReadU64_upd_self,
    envReadU64_upd_ne (ne_tmp_of_notTmp hynt 0), envReadU64_upd_ne (ne_tmp_of_notTmp hynt 1),
    envReadU64_upd_ne (ne_tmp_of_notTmp hynt 2),
    envReadU64_upd_ne (show tmpName 0 ≠ tmpName 1 by decide)]
  rfl

/-- Progress of the `(~(0 ^ y)) & (0 - y)` half of the `bSltu 0 y` mask block. -/
theorem lower_nzr {env : SEnvScalar} {y : String} {wy : BitVec 64}
    (hy : envReadU64 env y = some wy) (hynt : ¬ isTmpName y) :
    (semLowerSExpr env 0
      (.SAnd (.SXor (.SXor (.SLit 0) (.SVar y)) (.SLit ones))
        (.SSub (.SLit 0) (.SVar y)))).isSome := by
  simp only [semLowerSExpr, binNode, hy, envReadU64_upd_self,
    envReadU64_upd_ne (ne_tmp_of_notTmp hynt 0), envReadU64_upd_ne (ne_tmp_of_notTmp hynt 1),
    envReadU64_upd_ne (ne_tmp_of_notTmp hynt 2), envReadU64_upd_ne (ne_tmp_of_notTmp hynt 3),
    envReadU64_upd_ne (ne_tmp_of_notTmp hynt 4),
    envReadU64_upd_ne (show tmpName 1 ≠ tmpName 2 by decide),
    envReadU64_upd_ne (show tmpName 3 ≠ tmpName 4 by decide),
    envReadU64_upd_ne (show tmpName 3 ≠ tmpName 5 by decide)]
  rfl

/-! ## 2. The canonical per-trip entry state -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of the `mpn_cmp` limb body at one trip: the
    result array at `rp`, the trip index at `idx`, the two operand arrays at
    `ap` / `bp`, the limb count at `n`. -/
def cmpEnv (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    SEnvScalar :=
  (((((emptyEnv.upd "n" (t := .sword 64) nv).upd
      "bp" (t := .memref NU) bp).upd
      "ap" (t := .memref NU) ap).upd
      "idx" (t := .sword 64) iv).upd "rp" (t := .memref NR) acc)

theorem consistentS_cmpEnv (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons ap (.cons bp (.cons nv .nil))))) (cmpEnv ap bp acc iv nv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind consistentS_empty "n" (t := .sword 64) nv)
    "bp" (t := .memref NU) bp) "ap" (t := .memref NU) ap)
    "idx" (t := .sword 64) iv) "rp" (t := .memref NR) acc

theorem cmpEnv_rp (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    cmpEnv ap bp acc iv nv "rp" = some ⟨.memref NR, acc⟩ := upd_self _ _ _

theorem cmpEnv_idx (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    cmpEnv ap bp acc iv nv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [cmpEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem cmpEnv_ap (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    cmpEnv ap bp acc iv nv "ap" = some ⟨.memref NU, ap⟩ := by
  rw [cmpEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem cmpEnv_bp (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    cmpEnv ap bp acc iv nv "bp" = some ⟨.memref NU, bp⟩ := by
  rw [cmpEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem cmpEnv_n (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    cmpEnv ap bp acc iv nv "n" = some ⟨.sword 64, nv⟩ := by
  rw [cmpEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 3. Coverage -/

/-- Literal bound for the all-ones mask. -/
theorem hones : ones < 2 ^ 64 := by decide

/-- The `mpn_cmp` limb body is covered straight-line `LowCT`: three index
    assignments, three dynamic array reads, three `ltuCmds` blocks, the mask
    select, one dynamic array write. -/
theorem cmpLimbBody_coveredS : IsCoveredS cmpLimbBodyLowCT :=
  .rSeq (.rScalarSetExpr _ _ ⟨nt_n, (by decide : (1 : Nat) < 2 ^ 64)⟩)
   (.rSeq (.rScalarSetExpr _ _
        ⟨nt_top, nt_idx⟩)
    (.rSeq (.rScalarSetExpr _ _ (by decide : (0 : Nat) < 2 ^ 64))
     (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rArrLoad _ _ _)
       (.rSeq (.rArrLoad _ _ _)
        -- ltuCmds "lt" x y
        (.rSeq (.rScalarSetExpr _ _
            ⟨⟨nt_x, hones⟩, nt_y⟩)
         (.rSeq (.rScalarSetExpr _ _
             ⟨⟨⟨nt_x, nt_y⟩, hones⟩,
               ⟨nt_x, nt_y⟩⟩)
          (.rSeq (.rScalarSetExpr _ _
              ⟨⟨⟨nt_ltq, nt_ltr⟩,
                  ⟨nt_ltq, nt_ltr⟩⟩,
                (by decide : (63 : Nat) < 2 ^ 64)⟩)
           -- ltuCmds "gt" y x
           (.rSeq (.rScalarSetExpr _ _
               ⟨⟨nt_y, hones⟩, nt_x⟩)
            (.rSeq (.rScalarSetExpr _ _
                ⟨⟨⟨nt_y, nt_x⟩, hones⟩,
                  ⟨nt_y, nt_x⟩⟩)
             (.rSeq (.rScalarSetExpr _ _
                 ⟨⟨⟨nt_gtq, nt_gtr⟩,
                     ⟨nt_gtq, nt_gtr⟩⟩,
                   (by decide : (63 : Nat) < 2 ^ 64)⟩)
              -- step := gt - lt
              (.rSeq (.rScalarSetExpr _ _
                  ⟨nt_gt, nt_lt⟩)
               -- ltuCmds "nz" 0 prev
               (.rSeq (.rScalarSetExpr _ _
                   ⟨⟨(by decide : (0 : Nat) < 2 ^ 64), hones⟩,
                     notTmp_of_headNe rfl (by decide)⟩)
                (.rSeq (.rScalarSetExpr _ _
                    ⟨⟨⟨(by decide : (0 : Nat) < 2 ^ 64), notTmp_of_headNe rfl (by decide)⟩, hones⟩,
                      ⟨(by decide : (0 : Nat) < 2 ^ 64), notTmp_of_headNe rfl (by decide)⟩⟩)
                 (.rSeq (.rScalarSetExpr _ _
                     ⟨⟨⟨nt_nzq, nt_nzr⟩,
                         ⟨nt_nzq, nt_nzr⟩⟩,
                       (by decide : (63 : Nat) < 2 ^ 64)⟩)
                  -- keep := nz - 1
                  (.rSeq (.rScalarSetExpr _ _
                      ⟨nt_nz, (by decide : (1 : Nat) < 2 ^ 64)⟩)
                   -- dif := step ^ prev
                   (.rSeq (.rScalarSetExpr _ _
                       ⟨notTmp_of_headNe rfl (by decide), notTmp_of_headNe rfl (by decide)⟩)
                    -- out := prev ^ (keep & dif)
                    (.rSeq (.rScalarSetExpr _ _
                        ⟨notTmp_of_headNe rfl (by decide),
                          ⟨notTmp_of_headNe rfl (by decide), nt_dif⟩⟩)
                     (.rArrStore _ _ _)))))))))))))))))))

/-- The limb body sits in the control-extended covered fragment. -/
theorem cmpLimbBody_covered : IsCoveredSCtl cmpLimbBodyLowCT := .ofStraight cmpLimbBody_coveredS

/-! ## 4. The front-compiled body -/

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_cmp` limb body, extracted through the structural front-success gate. -/
def cmpUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" cmpLimbBodyLowCT).get cmpFrontOk

/-- The equation `cmpRtProg_denote` takes as its hypothesis. -/
theorem cmpUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" cmpLimbBodyLowCT = some cmpUpdate :=
  (Option.some_get cmpFrontOk).symm

/-- The first operand-array argument (RSI). -/
abbrev apVar : Ctxt.Var Gouter AO := .there (.there .here)

/-- The second operand-array argument (RDX). -/
abbrev bpVar : Ctxt.Var Gouter AO := .there .here

/-! ## 5. The per-trip run of the limb body -/

/-- **The limb body computes one `cmpFoldStep`.** From the canonical entry state
    at trip `t` (with `n ≥ 1` and `t < n`), the source body's `semScalar` run
    terminates and leaves exactly the memref-carrier step's array in `rp`: the
    running comparison result folded with this trip's limb, at descending index
    `(n - 1) - t`. The per-command check of the seam, stepped through the twenty
    commands. -/
theorem cmpLimbBody_run (ap bp : Fin NU → BitVec 64) (acc : Fin NR → BitVec 64)
    (nv : BitVec 64) (tt : Nat) (hn : 0 < nv.toNat) (htt : tt < nv.toNat) :
    ∃ env', semScalar cmpLimbBodyLowCT (cmpEnv ap bp acc (BitVec.ofNat 64 tt) nv) = some env'
      ∧ env' "rp" = some ⟨.memref NR, cmpFoldStep ap bp (nv.toNat - 1) acc tt⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 tt with hivdef
  have hnLt := nv.isLt
  have httlt : tt < 2 ^ 64 := Nat.lt_trans htt hnLt
  have hivN : iv.toNat = tt := by rw [hivdef]; simp only [BitVec.toNat_ofNat]; omega
  have htopN : (nv - BitVec.ofNat 64 1).toNat = nv.toNat - 1 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hjN : ((nv - BitVec.ofNat 64 1) - iv).toNat = nv.toNat - 1 - tt := by
    rw [BitVec.toNat_sub, htopN, hivN]; omega
  have hzN : (BitVec.ofNat 64 0).toNat = 0 := by simp [BitVec.toNat_ofNat]
  have hbody : cmpLimbBodyLowCT = seqAll
    [ .RScalarSetExpr "top" (.SSub (.SVar "n") (.SLit 1))
    , .RScalarSetExpr "j" (.SSub (.SVar "top") (.SVar "idx"))
    , .RScalarSetExpr "z" (.SLit 0)
    , .RArrLoad ⟨"x", .TU64⟩ ⟨"ap", .TBytes (8 * NU)⟩ "j"
    , .RArrLoad ⟨"y", .TU64⟩ ⟨"bp", .TBytes (8 * NU)⟩ "j"
    , .RArrLoad ⟨"prev", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "z"
    , .RScalarSetExpr "ltq" (.SAnd (.SXor (.SVar "x") (.SLit ones)) (.SVar "y"))
    , .RScalarSetExpr "ltr" (.SAnd (.SXor (.SXor (.SVar "x") (.SVar "y")) (.SLit ones))
        (.SSub (.SVar "x") (.SVar "y")))
    , .RScalarSetExpr "lt" (.SShr (.SXor (.SXor (.SVar "ltq") (.SVar "ltr"))
        (.SAnd (.SVar "ltq") (.SVar "ltr"))) (.SLit 63))
    , .RScalarSetExpr "gtq" (.SAnd (.SXor (.SVar "y") (.SLit ones)) (.SVar "x"))
    , .RScalarSetExpr "gtr" (.SAnd (.SXor (.SXor (.SVar "y") (.SVar "x")) (.SLit ones))
        (.SSub (.SVar "y") (.SVar "x")))
    , .RScalarSetExpr "gt" (.SShr (.SXor (.SXor (.SVar "gtq") (.SVar "gtr"))
        (.SAnd (.SVar "gtq") (.SVar "gtr"))) (.SLit 63))
    , .RScalarSetExpr "step" (.SSub (.SVar "gt") (.SVar "lt"))
    , .RScalarSetExpr "nzq" (.SAnd (.SXor (.SLit 0) (.SLit ones)) (.SVar "prev"))
    , .RScalarSetExpr "nzr" (.SAnd (.SXor (.SXor (.SLit 0) (.SVar "prev")) (.SLit ones))
        (.SSub (.SLit 0) (.SVar "prev")))
    , .RScalarSetExpr "nz" (.SShr (.SXor (.SXor (.SVar "nzq") (.SVar "nzr"))
        (.SAnd (.SVar "nzq") (.SVar "nzr"))) (.SLit 63))
    , .RScalarSetExpr "keep" (.SSub (.SVar "nz") (.SLit 1))
    , .RScalarSetExpr "dif" (.SXor (.SVar "step") (.SVar "prev"))
    , .RScalarSetExpr "out" (.SXor (.SVar "prev") (.SAnd (.SVar "keep") (.SVar "dif")))
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "z" ⟨"out", .TU64⟩ ] := rfl
  -- step 1: top := n - 1
  obtain ⟨e1, hs1, h1top, hf1⟩ := semScalar_setExpr_run (y := "top")
    (lower_sub_lit 1 (envReadU64_of_bound (cmpEnv_n ap bp acc iv nv)) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound (cmpEnv_n ap bp acc iv nv)] at h1top
  have h1rp := (hf1 "rp" (nt_rp) (by decide)).trans (cmpEnv_rp ap bp acc iv nv)
  have h1idx := (hf1 "idx" (nt_idx) (by decide)).trans (cmpEnv_idx ap bp acc iv nv)
  have h1ap := (hf1 "ap" (nt_ap) (by decide)).trans (cmpEnv_ap ap bp acc iv nv)
  have h1bp := (hf1 "bp" (nt_bp) (by decide)).trans (cmpEnv_bp ap bp acc iv nv)
  -- step 2: j := top - idx
  obtain ⟨e2, hs2, h2j, hf2⟩ := semScalar_setExpr_run (y := "j")
    (lower_sub_vv (envReadU64_of_bound h1top) (envReadU64_of_bound h1idx))
  simp only [SExpr.evalBV, envReader_of_bound h1top, envReader_of_bound h1idx] at h2j
  have h2rp := (hf2 "rp" (nt_rp) (by decide)).trans h1rp
  have h2ap := (hf2 "ap" (nt_ap) (by decide)).trans h1ap
  have h2bp := (hf2 "bp" (nt_bp) (by decide)).trans h1bp
  -- step 3: z := 0
  obtain ⟨e3, hs3, h3z, hf3⟩ := semScalar_setExpr_run (y := "z") (lower_lit (env := e2) 0)
  simp only [SExpr.evalBV] at h3z
  have h3rp := (hf3 "rp" (nt_rp) (by decide)).trans h2rp
  have h3ap := (hf3 "ap" (nt_ap) (by decide)).trans h2ap
  have h3bp := (hf3 "bp" (nt_bp) (by decide)).trans h2bp
  have h3j := (hf3 "j" (nt_j) (by decide)).trans h2j
  -- step 4: x := ap[j]
  obtain ⟨e4, hs4, h4x, hf4⟩ :=
    semScalar_arrLoad (dstN := "x") (tw := .TBytes (8 * NU)) (idxN := "j") h3ap h3j
  rw [hjN] at h4x
  have h4rp := (hf4 "rp" (by decide)).trans h3rp
  have h4bp := (hf4 "bp" (by decide)).trans h3bp
  have h4j := (hf4 "j" (by decide)).trans h3j
  have h4z := (hf4 "z" (by decide)).trans h3z
  -- step 5: y := bp[j]
  obtain ⟨e5, hs5, h5y, hf5⟩ :=
    semScalar_arrLoad (dstN := "y") (tw := .TBytes (8 * NU)) (idxN := "j") h4bp h4j
  rw [hjN] at h5y
  have h5rp := (hf5 "rp" (by decide)).trans h4rp
  have h5z := (hf5 "z" (by decide)).trans h4z
  have h5x := (hf5 "x" (by decide)).trans h4x
  -- step 6: prev := rp[z]
  obtain ⟨e6, hs6, h6prev, hf6⟩ :=
    semScalar_arrLoad (dstN := "prev") (tw := .TBytes (8 * NR)) (idxN := "z") h5rp h5z
  have h6rp := (hf6 "rp" (by decide)).trans h5rp
  have h6z := (hf6 "z" (by decide)).trans h5z
  have h6x := (hf6 "x" (by decide)).trans h5x
  have h6y := (hf6 "y" (by decide)).trans h5y
  -- step 7: ltq := (~x) & y
  obtain ⟨e7, hs7, h7ltq, hf7⟩ := semScalar_setExpr_run (y := "ltq")
    (lower_cq ones (envReadU64_of_bound h6x) (envReadU64_of_bound h6y) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h6x, envReader_of_bound h6y] at h7ltq
  have h7rp := (hf7 "rp" (nt_rp) (by decide)).trans h6rp
  have h7z := (hf7 "z" (nt_z) (by decide)).trans h6z
  have h7x := (hf7 "x" (nt_x) (by decide)).trans h6x
  have h7y := (hf7 "y" (nt_y) (by decide)).trans h6y
  have h7prev := (hf7 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h6prev
  -- step 8: ltr := (~(x ^ y)) & (x - y)
  obtain ⟨e8, hs8, h8ltr, hf8⟩ := semScalar_setExpr_run (y := "ltr")
    (lower_cr ones (envReadU64_of_bound h7x) (envReadU64_of_bound h7y) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h7x, envReader_of_bound h7y] at h8ltr
  have h8rp := (hf8 "rp" (nt_rp) (by decide)).trans h7rp
  have h8z := (hf8 "z" (nt_z) (by decide)).trans h7z
  have h8x := (hf8 "x" (nt_x) (by decide)).trans h7x
  have h8y := (hf8 "y" (nt_y) (by decide)).trans h7y
  have h8prev := (hf8 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h7prev
  have h8ltq := (hf8 "ltq" (nt_ltq) (by decide)).trans h7ltq
  -- step 9: lt := ((ltq | ltr) >> 63) = bSltu x y
  obtain ⟨e9, hs9, h9lt, hf9⟩ := semScalar_setExpr_run (y := "lt")
    (lower_orshr 63 (envReadU64_of_bound h8ltq) (envReadU64_of_bound h8ltr) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h8ltq, envReader_of_bound h8ltr] at h9lt
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h9lt
  have h9rp := (hf9 "rp" (nt_rp) (by decide)).trans h8rp
  have h9z := (hf9 "z" (nt_z) (by decide)).trans h8z
  have h9x := (hf9 "x" (nt_x) (by decide)).trans h8x
  have h9y := (hf9 "y" (nt_y) (by decide)).trans h8y
  have h9prev := (hf9 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h8prev
  -- step 10: gtq := (~y) & x
  obtain ⟨e10, hs10, h10gtq, hf10⟩ := semScalar_setExpr_run (y := "gtq")
    (lower_cq ones (envReadU64_of_bound h9y) (envReadU64_of_bound h9x) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h9y, envReader_of_bound h9x] at h10gtq
  have h10rp := (hf10 "rp" (nt_rp) (by decide)).trans h9rp
  have h10z := (hf10 "z" (nt_z) (by decide)).trans h9z
  have h10x := (hf10 "x" (nt_x) (by decide)).trans h9x
  have h10y := (hf10 "y" (nt_y) (by decide)).trans h9y
  have h10prev := (hf10 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h9prev
  have h10lt := (hf10 "lt" (nt_lt) (by decide)).trans h9lt
  -- step 11: gtr := (~(y ^ x)) & (y - x)
  obtain ⟨e11, hs11, h11gtr, hf11⟩ := semScalar_setExpr_run (y := "gtr")
    (lower_cr ones (envReadU64_of_bound h10y) (envReadU64_of_bound h10x) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h10y, envReader_of_bound h10x] at h11gtr
  have h11rp := (hf11 "rp" (nt_rp) (by decide)).trans h10rp
  have h11z := (hf11 "z" (nt_z) (by decide)).trans h10z
  have h11prev := (hf11 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h10prev
  have h11lt := (hf11 "lt" (nt_lt) (by decide)).trans h10lt
  have h11gtq := (hf11 "gtq" (nt_gtq) (by decide)).trans h10gtq
  -- step 12: gt := ((gtq | gtr) >> 63) = bSltu y x
  obtain ⟨e12, hs12, h12gt, hf12⟩ := semScalar_setExpr_run (y := "gt")
    (lower_orshr 63 (envReadU64_of_bound h11gtq) (envReadU64_of_bound h11gtr) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h11gtq, envReader_of_bound h11gtr] at h12gt
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h12gt
  have h12rp := (hf12 "rp" (nt_rp) (by decide)).trans h11rp
  have h12z := (hf12 "z" (nt_z) (by decide)).trans h11z
  have h12prev := (hf12 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h11prev
  have h12lt := (hf12 "lt" (nt_lt) (by decide)).trans h11lt
  -- step 13: step := gt - lt
  obtain ⟨e13, hs13, h13step, hf13⟩ := semScalar_setExpr_run (y := "step")
    (lower_sub_vv (envReadU64_of_bound h12gt) (envReadU64_of_bound h12lt))
  simp only [SExpr.evalBV, envReader_of_bound h12gt, envReader_of_bound h12lt] at h13step
  have h13rp := (hf13 "rp" (nt_rp) (by decide)).trans h12rp
  have h13z := (hf13 "z" (nt_z) (by decide)).trans h12z
  have h13prev := (hf13 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h12prev
  -- step 14: nzq := (~0) & prev
  obtain ⟨e14, hs14, h14nzq, hf14⟩ := semScalar_setExpr_run (y := "nzq")
    (lower_nzq (envReadU64_of_bound h13prev) (notTmp_of_headNe rfl (by decide)))
  simp only [SExpr.evalBV, envReader_of_bound h13prev] at h14nzq
  have h14rp := (hf14 "rp" (nt_rp) (by decide)).trans h13rp
  have h14z := (hf14 "z" (nt_z) (by decide)).trans h13z
  have h14prev := (hf14 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h13prev
  have h14step := (hf14 "step" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h13step
  -- step 15: nzr := (~(0 ^ prev)) & (0 - prev)
  obtain ⟨e15, hs15, h15nzr, hf15⟩ := semScalar_setExpr_run (y := "nzr")
    (lower_nzr (envReadU64_of_bound h14prev) (notTmp_of_headNe rfl (by decide)))
  simp only [SExpr.evalBV, envReader_of_bound h14prev] at h15nzr
  have h15rp := (hf15 "rp" (nt_rp) (by decide)).trans h14rp
  have h15z := (hf15 "z" (nt_z) (by decide)).trans h14z
  have h15prev := (hf15 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h14prev
  have h15step := (hf15 "step" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h14step
  have h15nzq := (hf15 "nzq" (nt_nzq) (by decide)).trans h14nzq
  -- step 16: nz := ((nzq | nzr) >> 63) = bSltu 0 prev
  obtain ⟨e16, hs16, h16nz, hf16⟩ := semScalar_setExpr_run (y := "nz")
    (lower_orshr 63 (envReadU64_of_bound h15nzq) (envReadU64_of_bound h15nzr) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h15nzq, envReader_of_bound h15nzr] at h16nz
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h16nz
  have h16rp := (hf16 "rp" (nt_rp) (by decide)).trans h15rp
  have h16z := (hf16 "z" (nt_z) (by decide)).trans h15z
  have h16prev := (hf16 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h15prev
  have h16step := (hf16 "step" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h15step
  -- step 17: keep := nz - 1
  obtain ⟨e17, hs17, h17keep, hf17⟩ := semScalar_setExpr_run (y := "keep")
    (lower_sub_lit 1 (envReadU64_of_bound h16nz) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h16nz] at h17keep
  have h17rp := (hf17 "rp" (nt_rp) (by decide)).trans h16rp
  have h17z := (hf17 "z" (nt_z) (by decide)).trans h16z
  have h17prev := (hf17 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h16prev
  have h17step := (hf17 "step" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h16step
  -- step 18: dif := step ^ prev
  obtain ⟨e18, hs18, h18dif, hf18⟩ := semScalar_setExpr_run (y := "dif")
    (lower_xor_vv (envReadU64_of_bound h17step) (envReadU64_of_bound h17prev))
  simp only [SExpr.evalBV, envReader_of_bound h17step, envReader_of_bound h17prev] at h18dif
  have h18rp := (hf18 "rp" (nt_rp) (by decide)).trans h17rp
  have h18z := (hf18 "z" (nt_z) (by decide)).trans h17z
  have h18prev := (hf18 "prev" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h17prev
  have h18keep := (hf18 "keep" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h17keep
  -- step 19: out := prev ^ (keep & dif)
  obtain ⟨e19, hs19, h19out, hf19⟩ := semScalar_setExpr_run (y := "out")
    (lower_xor_and (envReadU64_of_bound h18prev) (envReadU64_of_bound h18keep)
      (envReadU64_of_bound h18dif) (notTmp_of_headNe rfl (by decide)))
  simp only [SExpr.evalBV, envReader_of_bound h18prev, envReader_of_bound h18keep,
    envReader_of_bound h18dif] at h19out
  have h19rp := (hf19 "rp" (nt_rp) (by decide)).trans h18rp
  have h19z := (hf19 "z" (nt_z) (by decide)).trans h18z
  -- step 20: rp[z] := out
  obtain ⟨e20, hs20, h20rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h19rp h19z h19out
  refine ⟨e20, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8, seqAll_step hs9,
      seqAll_step hs10, seqAll_step hs11, seqAll_step hs12, seqAll_step hs13,
      seqAll_step hs14, seqAll_step hs15, seqAll_step hs16, seqAll_step hs17,
      seqAll_step hs18, seqAll_step hs19]
    exact hs20
  · rw [h20rp, hzN]
    simp only [cmpFoldStep, cmpSelW, cmpStepW]
    rfl

/-! ## 6. The machine-level fold and value theorems -/

/-- **The runtime-trip `mpn_cmp` program denotes the memref-carrier fold.** The
    compiled program's denotation at any valuation is `cmpFold` of the argument
    registers — the trip count read from `n`, the operand arrays threaded as
    invariants, the one-word result array as the accumulator seed, descending
    from the top limb `n - 1`. No front-compilation hypothesis remains. -/
theorem cmpRtProg_fold (V : Ctxt.Valuation Gouter) :
    cmpRtProgOpt.map (fun c => ComL.denote c V)
      = some (cmpFold (apVar.lookup V) (bpVar.lookup V)
          ((cmpCount.lookup V).toNat - 1) (cmpCount.lookup V).toNat (cmpInit.lookup V)) := by
  rw [cmpRtProg_denote (update := cmpUpdate) cmpUpdate_eq V]
  refine congrArg some ?_
  have h64 := (cmpCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.memref NU, .memref NU, .sword 64]) vmBody "rp" cmpLimbBodyLowCT
    cmpLimbBody_covered
    (.cons (apVar.lookup V) (.cons (bpVar.lookup V) (.cons (cmpCount.lookup V) .nil)))
    (fun arr tt => cmpFoldStep (apVar.lookup V) (bpVar.lookup V)
      ((cmpCount.lookup V).toNat - 1) arr tt)
    (cmpCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        cmpLimbBody_run (apVar.lookup V) (bpVar.lookup V) arr (cmpCount.lookup V) tt
          (by omega) htt
      exact ⟨cmpEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt)
          (cmpCount.lookup V), env',
        consistentS_cmpEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt)
          (cmpCount.lookup V),
        hrun, hrp⟩)
    cmpUpdate_eq (cmpInit.lookup V)

/-- **The compiled `mpn_cmp` computes the comparison sign.** For a nonzero trip
    count and a zeroed result cell, the compiled program's result cell holds
    `cmpSign` of the two operands' `bignumVal` over the limbs `0, …, n - 1` — the
    model-level `cmpFold_val_full` read on the machine-level denotation through
    the seam. -/
theorem cmpRtProg_val (V : Ctxt.Valuation Gouter)
    (hn : 0 < (cmpCount.lookup V).toNat)
    (h0 : memGetDyn (cmpInit.lookup V) 0 = 0) :
    ∃ out : Fin NR → BitVec 64,
      cmpRtProgOpt.map (fun c => ComL.denote c V) = some out ∧
        memGetDyn out 0
          = cmpSign (bignumVal (segCells (apVar.lookup V) 0 (cmpCount.lookup V).toNat))
              (bignumVal (segCells (bpVar.lookup V) 0 (cmpCount.lookup V).toNat)) := by
  refine ⟨_, cmpRtProg_fold V, ?_⟩
  have htop : (cmpCount.lookup V).toNat - 1 + 1 = (cmpCount.lookup V).toNat := by omega
  have h := cmpFold_val_full (apVar.lookup V) (bpVar.lookup V)
    ((cmpCount.lookup V).toNat - 1) (cmpInit.lookup V) (by decide) h0
  rw [htop] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
