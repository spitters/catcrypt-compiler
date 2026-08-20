/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The `mpn_divrem_1` loop body against its source semantics

`MpnDivRem1FrontEmit.divRem1RtProg_denote` states the emitted runtime-trip loop's
denotation as the `JLoopBodyN` fold of `update`, under the hypothesis
`frontLoopBodyJ … = some update`. This module supplies that `update` — using the
structural front-success gate `MpnDivRem1FrontTotal.divFrontOk` rather than a body
reduction — runs the source `LowCT` limb body symbolically through `semScalar`
from the canonical per-trip entry state, and identifies each trip with the
Möller–Granlund reciprocal step `preinvStep` over the memref carrier.

The per-trip run is the finite per-command check: three index assignments, two
`RArrLoad`s (the running remainder cell `qp[rs]` and the dividend limb `up[j]`),
the widening reciprocal multiply (`SMul` / `SMulHiU`), three `ltuCmds` branch-free
comparison blocks, the mask corrections, and two `RArrStore`s (the quotient limb
to `qp[j]` and the new remainder to `qp[rs]`), each stepped by the waist lemmas of
`Secp256k1PointOpFrameRoundTrip`. The word identities it reuses are `hiU_eq` (the
`SMulHiU` evaluator is `mulHiW`) and `ltu_chain` (the emitted xor/and carry idiom
is `bSltu`), both from `MpnMul1FrontDenote`, plus `notW` (the `xor`-with-all-ones
complement idiom is `~~~`).

The word function the emitted body computes is `preinvStep`, not the exact
Euclidean step `divLimb`. `divFold_val` in `MpnDivRem1FrontEmit` is stated about
`divLimb`; identifying the reciprocal fold below with it is the Möller–Granlund
argument recorded as the undischarged `PreinvStepAgrees`. This module therefore
carries the fold to the reciprocal step and stops there.

## Main results

* `divLimbBody_coveredS` / `divLimbBody_covered` — the limb body is covered
  straight-line `LowCT`.
* `divUpdate` / `divUpdate_eq` — the front-compiled limb body and the equation
  discharging `divRem1RtProg_denote`'s hypothesis.
* `divLimbBody_run` — the per-trip `semScalar` run: from the canonical entry
  state at trip `t`, the body leaves `preinvFoldStep up dinv d (n-1) rs acc t`
  in `qp`.
* `divRtProg_fold` — the runtime-trip program's denotation is the `preinvFold`
  memref-carrier fold of the reciprocal step, with no remaining hypothesis.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (ones seqAll sv notE orE ltuCmds)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step lower_mul_vv lower_hiu_vv lower_add_vv lower_add_lit
   lower_cq lower_cr lower_orshr hiU_eq ltu_chain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (NU NR RS qpLoc upLoc divLimbBodyLowCT vmBody Gbody Gouter r64 AQ AU
   divRem1RtProgOpt divRem1RtProg_denote divCount divInit divInvs preinvStep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal (divFrontOk)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

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

/-- Progress of the nested word-add `(x + y) + z`. -/
theorem lower_add2 {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hzl : z.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SAdd (.SVar x) (.SVar y)) (.SVar z))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hzl 0), hz, envReadU64_upd_self]
  rfl

/-- Progress of the `x ^ lit` step (the parity flip `c3 = c2 ^ 1`). -/
theorem lower_xor_lit {env : SEnvScalar} {x : String} {wx : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SXor (.SVar x) (.SLit L))).isSome := by
  simp only [semLowerSExpr, hx, binNode, envReadU64_upd_ne (ne_tmp_of_short hxl 0),
    envReadU64_upd_self]
  rfl

/-- Progress of the two's-complement mask `(~x) + 1` the sign masks lower to. -/
theorem lower_notadd1 {env : SEnvScalar} {x : String} {wx : BitVec 64} (L1 L2 : Nat)
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SXor (.SVar x) (.SLit L1)) (.SLit L2))).isSome := by
  simp only [semLowerSExpr, hx, binNode, envReadU64_upd_ne (ne_tmp_of_short hxl 0),
    envReadU64_upd_self, envReadU64_upd_ne (show tmpName 1 ≠ tmpName 2 by decide)]
  rfl

/-- Progress of the masked-add `x + (y & z)` the remainder correction lowers to. -/
theorem lower_add_and {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SVar x) (.SAnd (.SVar y) (.SVar z)))).isSome := by
  simp only [semLowerSExpr, hx, hy, hz, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), envReadU64_upd_self]
  rfl

/-- Progress of the masked-subtract `x - (y & z)` the remainder correction lowers to. -/
theorem lower_sub_and {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SSub (.SVar x) (.SAnd (.SVar y) (.SVar z)))).isSome := by
  simp only [semLowerSExpr, hx, hy, hz, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), envReadU64_upd_self]
  rfl

/-- The `xor`-with-all-ones complement idiom is the bitwise `~~~`. -/
theorem notW (x : BitVec 64) : x ^^^ BitVec.ofNat 64 ones = ~~~ x := by
  simp only [ones]; bv_decide

/-! ## 2. The canonical per-trip entry state -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of the `mpn_divrem_1` limb body at one trip:
    the output array at `qp`, the trip index at `idx`, the divisor at `d`, its
    reciprocal at `dinv`, the limb count at `n`, the dividend array at `up`. -/
def divEnv (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) : SEnvScalar :=
  ((((((emptyEnv.upd "up" (t := .memref NU) up).upd
      "n" (t := .sword 64) nv).upd
      "dinv" (t := .sword 64) dinv).upd
      "d" (t := .sword 64) d).upd
      "idx" (t := .sword 64) iv).upd "qp" (t := .memref NR) acc)

theorem consistentS_divEnv (up : Fin NU → BitVec 64) (dinv d : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv nv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons d (.cons dinv (.cons nv (.cons up .nil))))))
      (divEnv up dinv d acc iv nv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind (consistentS_bind consistentS_empty "up" (t := .memref NU) up)
      "n" (t := .sword 64) nv) "dinv" (t := .sword 64) dinv)
    "d" (t := .sword 64) d) "idx" (t := .sword 64) iv) "qp" (t := .memref NR) acc

theorem divEnv_qp (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "qp" = some ⟨.memref NR, acc⟩ := upd_self _ _ _

theorem divEnv_idx (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [divEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem divEnv_d (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "d" = some ⟨.sword 64, d⟩ := by
  rw [divEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem divEnv_dinv (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "dinv" = some ⟨.sword 64, dinv⟩ := by
  rw [divEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

theorem divEnv_n (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "n" = some ⟨.sword 64, nv⟩ := by
  rw [divEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

theorem divEnv_up (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv nv : BitVec 64) :
    divEnv up dinv d acc iv nv "up" = some ⟨.memref NU, up⟩ := by
  rw [divEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide),
    upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 3. The reciprocal-step fold over the memref carrier -/

/-- One trip of the emitted loop on the accumulator array, over the reciprocal
    step `preinvStep`: at trip `t` the descending limb index is `j = top - t`;
    read the running remainder from cell `rs` and the dividend limb from `up[j]`,
    run the Möller–Granlund reciprocal step, write the quotient limb to cell `j`
    and the new remainder to cell `rs`. The `preinvStep` twin of the FrontEmit
    `divFoldStep` (which is stated over the exact Euclidean step `divLimb`). -/
def preinvFoldStep (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (top rs : Nat)
    (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn (memSetDyn acc (top - t)
      (preinvStep dinv d (memGetDyn acc rs) (memGetDyn up (top - t))).1)
    rs (preinvStep dinv d (memGetDyn acc rs) (memGetDyn up (top - t))).2

/-- The `k`-fold of `preinvFoldStep` over the trip indices `0, …, k-1`: the
    `(List.range k).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.memref NR`. -/
def preinvFold (up : Fin NU → BitVec 64) (dinv d : BitVec 64) (top rs k : Nat)
    (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range k).foldl (preinvFoldStep up dinv d top rs) acc

/-! ## 4. Coverage -/

/-- Literal bound for the all-ones mask. -/
theorem hones : ones < 2 ^ 64 := by decide

/-- The `mpn_divrem_1` limb body is covered straight-line `LowCT`. -/
theorem divLimbBody_coveredS : IsCoveredS divLimbBodyLowCT :=
  .rSeq (.rScalarSetExpr _ _ ⟨notTmp_of_short "n" (by decide), (by decide : (1 : Nat) < 2 ^ 64)⟩)
   (.rSeq (.rScalarSetExpr _ _
        ⟨notTmp_of_short "top" (by decide), notTmp_of_short "idx" (by decide)⟩)
    (.rSeq (.rScalarSetExpr _ _ (by decide : (RS : Nat) < 2 ^ 64))
     (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rArrLoad _ _ _)
       (.rSeq (.rScalarSetExpr _ _
            ⟨notTmp_of_headNe rfl (by decide), notTmp_of_short "u1" (by decide)⟩)
        (.rSeq (.rScalarSetExpr _ _
             ⟨notTmp_of_headNe rfl (by decide), notTmp_of_short "u1" (by decide)⟩)
         (.rSeq (.rScalarSetExpr _ _
              ⟨notTmp_of_short "ql" (by decide), notTmp_of_short "u0" (by decide)⟩)
          -- ltuCmds "c0" qla ql
          (.rSeq (.rScalarSetExpr _ _
               ⟨⟨notTmp_of_short "qla" (by decide), hones⟩, notTmp_of_short "ql" (by decide)⟩)
           (.rSeq (.rScalarSetExpr _ _
                ⟨⟨⟨notTmp_of_short "qla" (by decide), notTmp_of_short "ql" (by decide)⟩, hones⟩,
                  ⟨notTmp_of_short "qla" (by decide), notTmp_of_short "ql" (by decide)⟩⟩)
            (.rSeq (.rScalarSetExpr _ _
                 ⟨⟨⟨notTmp_of_short "c0q" (by decide), notTmp_of_short "c0r" (by decide)⟩,
                     ⟨notTmp_of_short "c0q" (by decide), notTmp_of_short "c0r" (by decide)⟩⟩,
                   (by decide : (63 : Nat) < 2 ^ 64)⟩)
             (.rSeq (.rScalarSetExpr _ _
                  ⟨notTmp_of_short "u1" (by decide), (by decide : (1 : Nat) < 2 ^ 64)⟩)
              (.rSeq (.rScalarSetExpr _ _
                   ⟨⟨notTmp_of_short "qh" (by decide), notTmp_of_short "u1p" (by decide)⟩,
                     notTmp_of_short "c0" (by decide)⟩)
               (.rSeq (.rScalarSetExpr _ _
                    ⟨notTmp_of_short "qhb" (by decide), notTmp_of_short "d" (by decide)⟩)
                (.rSeq (.rScalarSetExpr _ _
                     ⟨notTmp_of_short "u0" (by decide), notTmp_of_short "p" (by decide)⟩)
                 -- ltuCmds "c1" qla r
                 (.rSeq (.rScalarSetExpr _ _
                      ⟨⟨notTmp_of_short "qla" (by decide), hones⟩, notTmp_of_short "r" (by decide)⟩)
                  (.rSeq (.rScalarSetExpr _ _
                       ⟨⟨⟨notTmp_of_short "qla" (by decide), notTmp_of_short "r" (by decide)⟩, hones⟩,
                         ⟨notTmp_of_short "qla" (by decide), notTmp_of_short "r" (by decide)⟩⟩)
                   (.rSeq (.rScalarSetExpr _ _
                        ⟨⟨⟨notTmp_of_short "c1q" (by decide), notTmp_of_short "c1r" (by decide)⟩,
                            ⟨notTmp_of_short "c1q" (by decide), notTmp_of_short "c1r" (by decide)⟩⟩,
                          (by decide : (63 : Nat) < 2 ^ 64)⟩)
                    (.rSeq (.rScalarSetExpr _ _
                         ⟨⟨notTmp_of_short "c1" (by decide), hones⟩, (by decide : (1 : Nat) < 2 ^ 64)⟩)
                     (.rSeq (.rScalarSetExpr _ _
                          ⟨notTmp_of_short "qhb" (by decide), notTmp_of_short "m1" (by decide)⟩)
                      (.rSeq (.rScalarSetExpr _ _
                           ⟨notTmp_of_short "r" (by decide),
                             ⟨notTmp_of_short "m1" (by decide), notTmp_of_short "d" (by decide)⟩⟩)
                       -- ltuCmds "c2" ra d
                       (.rSeq (.rScalarSetExpr _ _
                            ⟨⟨notTmp_of_short "ra" (by decide), hones⟩, notTmp_of_short "d" (by decide)⟩)
                        (.rSeq (.rScalarSetExpr _ _
                             ⟨⟨⟨notTmp_of_short "ra" (by decide), notTmp_of_short "d" (by decide)⟩, hones⟩,
                               ⟨notTmp_of_short "ra" (by decide), notTmp_of_short "d" (by decide)⟩⟩)
                         (.rSeq (.rScalarSetExpr _ _
                              ⟨⟨⟨notTmp_of_short "c2q" (by decide), notTmp_of_short "c2r" (by decide)⟩,
                                  ⟨notTmp_of_short "c2q" (by decide), notTmp_of_short "c2r" (by decide)⟩⟩,
                                (by decide : (63 : Nat) < 2 ^ 64)⟩)
                          (.rSeq (.rScalarSetExpr _ _
                               ⟨notTmp_of_short "c2" (by decide), (by decide : (1 : Nat) < 2 ^ 64)⟩)
                           (.rSeq (.rScalarSetExpr _ _
                                ⟨⟨notTmp_of_short "c3" (by decide), hones⟩, (by decide : (1 : Nat) < 2 ^ 64)⟩)
                            (.rSeq (.rScalarSetExpr _ _
                                 ⟨notTmp_of_short "qhc" (by decide), notTmp_of_short "c3" (by decide)⟩)
                             (.rSeq (.rScalarSetExpr _ _
                                  ⟨notTmp_of_short "ra" (by decide),
                                    ⟨notTmp_of_short "m3" (by decide), notTmp_of_short "d" (by decide)⟩⟩)
                              (.rSeq (.rArrStore _ _ _)
                               (.rArrStore _ _ _)))))))))))))))))))))))))))))

/-- The limb body sits in the control-extended covered fragment. -/
theorem divLimbBody_covered : IsCoveredSCtl divLimbBodyLowCT := .ofStraight divLimbBody_coveredS

/-! ## 5. The front-compiled body -/

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_divrem_1` limb body, extracted through the structural front-success gate. -/
def divUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "qp" divLimbBodyLowCT).get divFrontOk

/-- The equation `divRem1RtProg_denote` takes as its hypothesis. -/
theorem divUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "qp" divLimbBodyLowCT = some divUpdate :=
  (Option.some_get divFrontOk).symm

/-! ## 6. The outer argument registers -/

/-- The divisor argument `d` (RCX). -/
abbrev dVar : Ctxt.Var Gouter r64 := .there .here

/-- The reciprocal argument `dinv` (R8). -/
abbrev dinvVar : Ctxt.Var Gouter r64 := .here

/-- The limb-count argument `n` (RDX). -/
abbrev nVar : Ctxt.Var Gouter r64 := .there (.there .here)

/-- The dividend-array argument `up` (RSI). -/
abbrev upVar : Ctxt.Var Gouter AU := .there (.there (.there .here))

/-! ## 7. The per-trip run of the limb body -/

/-- **The limb body computes one `preinvFoldStep`.** From the canonical entry
    state at trip `t` (with `n ≥ 1` and `t < n`), the source body's `semScalar`
    run terminates and leaves exactly the reciprocal step's array in `qp`: the
    quotient limb at descending index `(n - 1) - t` and the running remainder at
    cell `RS`, produced by the Möller–Granlund reciprocal step `preinvStep`. The
    per-command check of the seam, stepped through the thirty commands. -/
theorem divLimbBody_run (up : Fin NU → BitVec 64) (dinv d : BitVec 64)
    (acc : Fin NR → BitVec 64) (nv : BitVec 64) (tt : Nat) (hn : 0 < nv.toNat)
    (htt : tt < nv.toNat) :
    ∃ env', semScalar divLimbBodyLowCT (divEnv up dinv d acc (BitVec.ofNat 64 tt) nv) = some env'
      ∧ env' "qp" = some ⟨.memref NR, preinvFoldStep up dinv d (nv.toNat - 1) RS acc tt⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 tt with hivdef
  have hnLt := nv.isLt
  have httlt : tt < 2 ^ 64 := Nat.lt_trans htt hnLt
  have hivN : iv.toNat = tt := by rw [hivdef]; simp only [BitVec.toNat_ofNat]; omega
  have htopN : (nv - BitVec.ofNat 64 1).toNat = nv.toNat - 1 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hjN : ((nv - BitVec.ofNat 64 1) - iv).toNat = nv.toNat - 1 - tt := by
    rw [BitVec.toNat_sub, htopN, hivN]; omega
  have hrsN : (BitVec.ofNat 64 RS).toNat = RS := by decide
  have hbody : divLimbBodyLowCT = seqAll
    [ .RScalarSetExpr "top" (.SSub (.SVar "n") (.SLit 1))
    , .RScalarSetExpr "j" (.SSub (.SVar "top") (.SVar "idx"))
    , .RScalarSetExpr "rs" (.SLit RS)
    , .RArrLoad ⟨"u1", .TU64⟩ ⟨"qp", .TBytes (8 * NR)⟩ "rs"
    , .RArrLoad ⟨"u0", .TU64⟩ ⟨"up", .TBytes (8 * NU)⟩ "j"
    , .RScalarSetExpr "ql" (.SMul (.SVar "dinv") (.SVar "u1"))
    , .RScalarSetExpr "qh" (.SMulHiU (.SVar "dinv") (.SVar "u1"))
    , .RScalarSetExpr "qla" (.SAdd (.SVar "ql") (.SVar "u0"))
    , .RScalarSetExpr "c0q" (.SAnd (.SXor (.SVar "qla") (.SLit ones)) (.SVar "ql"))
    , .RScalarSetExpr "c0r" (.SAnd (.SXor (.SXor (.SVar "qla") (.SVar "ql")) (.SLit ones))
        (.SSub (.SVar "qla") (.SVar "ql")))
    , .RScalarSetExpr "c0" (.SShr (.SXor (.SXor (.SVar "c0q") (.SVar "c0r"))
        (.SAnd (.SVar "c0q") (.SVar "c0r"))) (.SLit 63))
    , .RScalarSetExpr "u1p" (.SAdd (.SVar "u1") (.SLit 1))
    , .RScalarSetExpr "qhb" (.SAdd (.SAdd (.SVar "qh") (.SVar "u1p")) (.SVar "c0"))
    , .RScalarSetExpr "p" (.SMul (.SVar "qhb") (.SVar "d"))
    , .RScalarSetExpr "r" (.SSub (.SVar "u0") (.SVar "p"))
    , .RScalarSetExpr "c1q" (.SAnd (.SXor (.SVar "qla") (.SLit ones)) (.SVar "r"))
    , .RScalarSetExpr "c1r" (.SAnd (.SXor (.SXor (.SVar "qla") (.SVar "r")) (.SLit ones))
        (.SSub (.SVar "qla") (.SVar "r")))
    , .RScalarSetExpr "c1" (.SShr (.SXor (.SXor (.SVar "c1q") (.SVar "c1r"))
        (.SAnd (.SVar "c1q") (.SVar "c1r"))) (.SLit 63))
    , .RScalarSetExpr "m1" (.SAdd (.SXor (.SVar "c1") (.SLit ones)) (.SLit 1))
    , .RScalarSetExpr "qhc" (.SAdd (.SVar "qhb") (.SVar "m1"))
    , .RScalarSetExpr "ra" (.SAdd (.SVar "r") (.SAnd (.SVar "m1") (.SVar "d")))
    , .RScalarSetExpr "c2q" (.SAnd (.SXor (.SVar "ra") (.SLit ones)) (.SVar "d"))
    , .RScalarSetExpr "c2r" (.SAnd (.SXor (.SXor (.SVar "ra") (.SVar "d")) (.SLit ones))
        (.SSub (.SVar "ra") (.SVar "d")))
    , .RScalarSetExpr "c2" (.SShr (.SXor (.SXor (.SVar "c2q") (.SVar "c2r"))
        (.SAnd (.SVar "c2q") (.SVar "c2r"))) (.SLit 63))
    , .RScalarSetExpr "c3" (.SXor (.SVar "c2") (.SLit 1))
    , .RScalarSetExpr "m3" (.SAdd (.SXor (.SVar "c3") (.SLit ones)) (.SLit 1))
    , .RScalarSetExpr "qout" (.SAdd (.SVar "qhc") (.SVar "c3"))
    , .RScalarSetExpr "rout" (.SSub (.SVar "ra") (.SAnd (.SVar "m3") (.SVar "d")))
    , .RArrStore ⟨"qp", .TBytes (8 * NR)⟩ "j" ⟨"qout", .TU64⟩
    , .RArrStore ⟨"qp", .TBytes (8 * NR)⟩ "rs" ⟨"rout", .TU64⟩ ] := rfl
  -- step 1: top := n - 1
  obtain ⟨e1, hs1, h1top, hf1⟩ := semScalar_setExpr_run (y := "top")
    (lower_sub_lit 1 (envReadU64_of_bound (divEnv_n up dinv d acc iv nv)) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound (divEnv_n up dinv d acc iv nv)] at h1top
  have h1qp := (hf1 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans (divEnv_qp up dinv d acc iv nv)
  have h1idx := (hf1 "idx" (notTmp_of_short "idx" (by decide)) (by decide)).trans (divEnv_idx up dinv d acc iv nv)
  have h1d := (hf1 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans (divEnv_d up dinv d acc iv nv)
  have h1dinv := (hf1 "dinv" (notTmp_of_headNe rfl (by decide)) (by decide)).trans (divEnv_dinv up dinv d acc iv nv)
  have h1up := (hf1 "up" (notTmp_of_short "up" (by decide)) (by decide)).trans (divEnv_up up dinv d acc iv nv)
  -- step 2: j := top - idx
  obtain ⟨e2, hs2, h2j, hf2⟩ := semScalar_setExpr_run (y := "j")
    (lower_sub_vv (envReadU64_of_bound h1top) (envReadU64_of_bound h1idx))
  simp only [SExpr.evalBV, envReader_of_bound h1top, envReader_of_bound h1idx] at h2j
  have h2qp := (hf2 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h1qp
  have h2d := (hf2 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h1d
  have h2dinv := (hf2 "dinv" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h1dinv
  have h2up := (hf2 "up" (notTmp_of_short "up" (by decide)) (by decide)).trans h1up
  -- step 3: rs := RS
  obtain ⟨e3, hs3, h3rs, hf3⟩ := semScalar_setExpr_run (y := "rs") (lower_lit (env := e2) RS)
  simp only [SExpr.evalBV] at h3rs
  have h3qp := (hf3 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h2qp
  have h3j := (hf3 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h2j
  have h3d := (hf3 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h2d
  have h3dinv := (hf3 "dinv" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h2dinv
  have h3up := (hf3 "up" (notTmp_of_short "up" (by decide)) (by decide)).trans h2up
  -- step 4: u1 := qp[rs]
  obtain ⟨e4, hs4, h4u1, hf4⟩ :=
    semScalar_arrLoad (dstN := "u1") (tw := .TBytes (8 * NR)) (idxN := "rs") h3qp h3rs
  rw [hrsN] at h4u1
  have h4qp := (hf4 "qp" (by decide)).trans h3qp
  have h4j := (hf4 "j" (by decide)).trans h3j
  have h4rs := (hf4 "rs" (by decide)).trans h3rs
  have h4d := (hf4 "d" (by decide)).trans h3d
  have h4dinv := (hf4 "dinv" (by decide)).trans h3dinv
  have h4up := (hf4 "up" (by decide)).trans h3up
  -- step 5: u0 := up[j]
  obtain ⟨e5, hs5, h5u0, hf5⟩ :=
    semScalar_arrLoad (dstN := "u0") (tw := .TBytes (8 * NU)) (idxN := "j") h4up h4j
  rw [hjN] at h5u0
  have h5qp := (hf5 "qp" (by decide)).trans h4qp
  have h5j := (hf5 "j" (by decide)).trans h4j
  have h5rs := (hf5 "rs" (by decide)).trans h4rs
  have h5d := (hf5 "d" (by decide)).trans h4d
  have h5dinv := (hf5 "dinv" (by decide)).trans h4dinv
  have h5u1 := (hf5 "u1" (by decide)).trans h4u1
  -- step 6: ql := dinv * u1
  obtain ⟨e6, hs6, h6ql, hf6⟩ := semScalar_setExpr_run (y := "ql")
    (lower_mul_vv (envReadU64_of_bound h5dinv) (envReadU64_of_bound h5u1))
  simp only [SExpr.evalBV, envReader_of_bound h5dinv, envReader_of_bound h5u1] at h6ql
  have h6qp := (hf6 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h5qp
  have h6j := (hf6 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h5j
  have h6rs := (hf6 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h5rs
  have h6d := (hf6 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h5d
  have h6dinv := (hf6 "dinv" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h5dinv
  have h6u1 := (hf6 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h5u1
  have h6u0 := (hf6 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h5u0
  -- step 7: qh := mulhi(dinv, u1)
  obtain ⟨e7, hs7, h7qh, hf7⟩ := semScalar_setExpr_run (y := "qh")
    (lower_hiu_vv (envReadU64_of_bound h6dinv) (envReadU64_of_bound h6u1))
  simp only [SExpr.evalBV, envReader_of_bound h6dinv, envReader_of_bound h6u1, hiU_eq] at h7qh
  have h7qp := (hf7 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h6qp
  have h7j := (hf7 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h6j
  have h7rs := (hf7 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h6rs
  have h7d := (hf7 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h6d
  have h7u1 := (hf7 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h6u1
  have h7u0 := (hf7 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h6u0
  have h7ql := (hf7 "ql" (notTmp_of_short "ql" (by decide)) (by decide)).trans h6ql
  -- step 8: qla := ql + u0
  obtain ⟨e8, hs8, h8qla, hf8⟩ := semScalar_setExpr_run (y := "qla")
    (lower_add_vv (envReadU64_of_bound h7ql) (envReadU64_of_bound h7u0))
  simp only [SExpr.evalBV, envReader_of_bound h7ql, envReader_of_bound h7u0] at h8qla
  have h8qp := (hf8 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h7qp
  have h8j := (hf8 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h7j
  have h8rs := (hf8 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h7rs
  have h8d := (hf8 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h7d
  have h8u1 := (hf8 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h7u1
  have h8u0 := (hf8 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h7u0
  have h8ql := (hf8 "ql" (notTmp_of_short "ql" (by decide)) (by decide)).trans h7ql
  have h8qh := (hf8 "qh" (notTmp_of_short "qh" (by decide)) (by decide)).trans h7qh
  -- step 9: c0q := (~qla) & ql
  obtain ⟨e9, hs9, h9c0q, hf9⟩ := semScalar_setExpr_run (y := "c0q")
    (lower_cq ones (envReadU64_of_bound h8qla) (envReadU64_of_bound h8ql) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h8qla, envReader_of_bound h8ql] at h9c0q
  have h9qp := (hf9 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h8qp
  have h9j := (hf9 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h8j
  have h9rs := (hf9 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h8rs
  have h9d := (hf9 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h8d
  have h9u1 := (hf9 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h8u1
  have h9u0 := (hf9 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h8u0
  have h9ql := (hf9 "ql" (notTmp_of_short "ql" (by decide)) (by decide)).trans h8ql
  have h9qh := (hf9 "qh" (notTmp_of_short "qh" (by decide)) (by decide)).trans h8qh
  have h9qla := (hf9 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h8qla
  -- step 10: c0r := (~(qla ^ ql)) & (qla - ql)
  obtain ⟨e10, hs10, h10c0r, hf10⟩ := semScalar_setExpr_run (y := "c0r")
    (lower_cr ones (envReadU64_of_bound h9qla) (envReadU64_of_bound h9ql) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h9qla, envReader_of_bound h9ql] at h10c0r
  have h10qp := (hf10 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h9qp
  have h10j := (hf10 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h9j
  have h10rs := (hf10 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h9rs
  have h10d := (hf10 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h9d
  have h10u1 := (hf10 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h9u1
  have h10u0 := (hf10 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h9u0
  have h10qh := (hf10 "qh" (notTmp_of_short "qh" (by decide)) (by decide)).trans h9qh
  have h10qla := (hf10 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h9qla
  have h10c0q := (hf10 "c0q" (notTmp_of_short "c0q" (by decide)) (by decide)).trans h9c0q
  -- step 11: c0 := ((c0q | c0r) >> 63) = bSltu qla ql
  obtain ⟨e11, hs11, h11c0, hf11⟩ := semScalar_setExpr_run (y := "c0")
    (lower_orshr 63 (envReadU64_of_bound h10c0q) (envReadU64_of_bound h10c0r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h10c0q, envReader_of_bound h10c0r] at h11c0
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h11c0
  have h11qp := (hf11 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h10qp
  have h11j := (hf11 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h10j
  have h11rs := (hf11 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h10rs
  have h11d := (hf11 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h10d
  have h11u1 := (hf11 "u1" (notTmp_of_short "u1" (by decide)) (by decide)).trans h10u1
  have h11u0 := (hf11 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h10u0
  have h11qh := (hf11 "qh" (notTmp_of_short "qh" (by decide)) (by decide)).trans h10qh
  have h11qla := (hf11 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h10qla
  -- step 12: u1p := u1 + 1
  obtain ⟨e12, hs12, h12u1p, hf12⟩ := semScalar_setExpr_run (y := "u1p")
    (lower_add_lit 1 (envReadU64_of_bound h11u1) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h11u1] at h12u1p
  have h12qp := (hf12 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h11qp
  have h12j := (hf12 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h11j
  have h12rs := (hf12 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h11rs
  have h12d := (hf12 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h11d
  have h12u0 := (hf12 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h11u0
  have h12qh := (hf12 "qh" (notTmp_of_short "qh" (by decide)) (by decide)).trans h11qh
  have h12qla := (hf12 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h11qla
  have h12c0 := (hf12 "c0" (notTmp_of_short "c0" (by decide)) (by decide)).trans h11c0
  -- step 13: qhb := (qh + u1p) + c0
  obtain ⟨e13, hs13, h13qhb, hf13⟩ := semScalar_setExpr_run (y := "qhb")
    (lower_add2 (envReadU64_of_bound h12qh) (envReadU64_of_bound h12u1p)
      (envReadU64_of_bound h12c0) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h12qh, envReader_of_bound h12u1p,
    envReader_of_bound h12c0] at h13qhb
  have h13qp := (hf13 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h12qp
  have h13j := (hf13 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h12j
  have h13rs := (hf13 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h12rs
  have h13d := (hf13 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h12d
  have h13u0 := (hf13 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h12u0
  have h13qla := (hf13 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h12qla
  -- step 14: p := qhb * d
  obtain ⟨e14, hs14, h14p, hf14⟩ := semScalar_setExpr_run (y := "p")
    (lower_mul_vv (envReadU64_of_bound h13qhb) (envReadU64_of_bound h13d))
  simp only [SExpr.evalBV, envReader_of_bound h13qhb, envReader_of_bound h13d] at h14p
  have h14qp := (hf14 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h13qp
  have h14j := (hf14 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h13j
  have h14rs := (hf14 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h13rs
  have h14d := (hf14 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h13d
  have h14u0 := (hf14 "u0" (notTmp_of_short "u0" (by decide)) (by decide)).trans h13u0
  have h14qla := (hf14 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h13qla
  have h14qhb := (hf14 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h13qhb
  -- step 15: r := u0 - p
  obtain ⟨e15, hs15, h15r, hf15⟩ := semScalar_setExpr_run (y := "r")
    (lower_sub_vv (envReadU64_of_bound h14u0) (envReadU64_of_bound h14p))
  simp only [SExpr.evalBV, envReader_of_bound h14u0, envReader_of_bound h14p] at h15r
  have h15qp := (hf15 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h14qp
  have h15j := (hf15 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h14j
  have h15rs := (hf15 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h14rs
  have h15d := (hf15 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h14d
  have h15qla := (hf15 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h14qla
  have h15qhb := (hf15 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h14qhb
  -- step 16: c1q := (~qla) & r
  obtain ⟨e16, hs16, h16c1q, hf16⟩ := semScalar_setExpr_run (y := "c1q")
    (lower_cq ones (envReadU64_of_bound h15qla) (envReadU64_of_bound h15r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h15qla, envReader_of_bound h15r] at h16c1q
  have h16qp := (hf16 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h15qp
  have h16j := (hf16 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h15j
  have h16rs := (hf16 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h15rs
  have h16d := (hf16 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h15d
  have h16qla := (hf16 "qla" (notTmp_of_short "qla" (by decide)) (by decide)).trans h15qla
  have h16qhb := (hf16 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h15qhb
  have h16r := (hf16 "r" (notTmp_of_short "r" (by decide)) (by decide)).trans h15r
  -- step 17: c1r := (~(qla ^ r)) & (qla - r)
  obtain ⟨e17, hs17, h17c1r, hf17⟩ := semScalar_setExpr_run (y := "c1r")
    (lower_cr ones (envReadU64_of_bound h16qla) (envReadU64_of_bound h16r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h16qla, envReader_of_bound h16r] at h17c1r
  have h17qp := (hf17 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h16qp
  have h17j := (hf17 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h16j
  have h17rs := (hf17 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h16rs
  have h17d := (hf17 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h16d
  have h17qhb := (hf17 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h16qhb
  have h17r := (hf17 "r" (notTmp_of_short "r" (by decide)) (by decide)).trans h16r
  have h17c1q := (hf17 "c1q" (notTmp_of_short "c1q" (by decide)) (by decide)).trans h16c1q
  -- step 18: c1 := ((c1q | c1r) >> 63) = bSltu qla r
  obtain ⟨e18, hs18, h18c1, hf18⟩ := semScalar_setExpr_run (y := "c1")
    (lower_orshr 63 (envReadU64_of_bound h17c1q) (envReadU64_of_bound h17c1r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h17c1q, envReader_of_bound h17c1r] at h18c1
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h18c1
  have h18qp := (hf18 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h17qp
  have h18j := (hf18 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h17j
  have h18rs := (hf18 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h17rs
  have h18d := (hf18 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h17d
  have h18qhb := (hf18 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h17qhb
  have h18r := (hf18 "r" (notTmp_of_short "r" (by decide)) (by decide)).trans h17r
  -- step 19: m1 := (~c1) + 1
  obtain ⟨e19, hs19, h19m1, hf19⟩ := semScalar_setExpr_run (y := "m1")
    (lower_notadd1 ones 1 (envReadU64_of_bound h18c1) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h18c1] at h19m1
  rw [notW] at h19m1
  have h19qp := (hf19 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h18qp
  have h19j := (hf19 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h18j
  have h19rs := (hf19 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h18rs
  have h19d := (hf19 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h18d
  have h19qhb := (hf19 "qhb" (notTmp_of_short "qhb" (by decide)) (by decide)).trans h18qhb
  have h19r := (hf19 "r" (notTmp_of_short "r" (by decide)) (by decide)).trans h18r
  -- step 20: qhc := qhb + m1
  obtain ⟨e20, hs20, h20qhc, hf20⟩ := semScalar_setExpr_run (y := "qhc")
    (lower_add_vv (envReadU64_of_bound h19qhb) (envReadU64_of_bound h19m1))
  simp only [SExpr.evalBV, envReader_of_bound h19qhb, envReader_of_bound h19m1] at h20qhc
  have h20qp := (hf20 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h19qp
  have h20j := (hf20 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h19j
  have h20rs := (hf20 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h19rs
  have h20d := (hf20 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h19d
  have h20r := (hf20 "r" (notTmp_of_short "r" (by decide)) (by decide)).trans h19r
  have h20m1 := (hf20 "m1" (notTmp_of_short "m1" (by decide)) (by decide)).trans h19m1
  -- step 21: ra := r + (m1 & d)
  obtain ⟨e21, hs21, h21ra, hf21⟩ := semScalar_setExpr_run (y := "ra")
    (lower_add_and (envReadU64_of_bound h20r) (envReadU64_of_bound h20m1)
      (envReadU64_of_bound h20d) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h20r, envReader_of_bound h20m1,
    envReader_of_bound h20d] at h21ra
  have h21qp := (hf21 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h20qp
  have h21j := (hf21 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h20j
  have h21rs := (hf21 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h20rs
  have h21d := (hf21 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h20d
  have h21qhc := (hf21 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h20qhc
  -- step 22: c2q := (~ra) & d
  obtain ⟨e22, hs22, h22c2q, hf22⟩ := semScalar_setExpr_run (y := "c2q")
    (lower_cq ones (envReadU64_of_bound h21ra) (envReadU64_of_bound h21d) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h21ra, envReader_of_bound h21d] at h22c2q
  have h22qp := (hf22 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h21qp
  have h22j := (hf22 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h21j
  have h22rs := (hf22 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h21rs
  have h22d := (hf22 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h21d
  have h22qhc := (hf22 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h21qhc
  have h22ra := (hf22 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h21ra
  -- step 23: c2r := (~(ra ^ d)) & (ra - d)
  obtain ⟨e23, hs23, h23c2r, hf23⟩ := semScalar_setExpr_run (y := "c2r")
    (lower_cr ones (envReadU64_of_bound h22ra) (envReadU64_of_bound h22d) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h22ra, envReader_of_bound h22d] at h23c2r
  have h23qp := (hf23 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h22qp
  have h23j := (hf23 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h22j
  have h23rs := (hf23 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h22rs
  have h23d := (hf23 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h22d
  have h23qhc := (hf23 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h22qhc
  have h23ra := (hf23 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h22ra
  have h23c2q := (hf23 "c2q" (notTmp_of_short "c2q" (by decide)) (by decide)).trans h22c2q
  -- step 24: c2 := ((c2q | c2r) >> 63) = bSltu ra d
  obtain ⟨e24, hs24, h24c2, hf24⟩ := semScalar_setExpr_run (y := "c2")
    (lower_orshr 63 (envReadU64_of_bound h23c2q) (envReadU64_of_bound h23c2r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h23c2q, envReader_of_bound h23c2r] at h24c2
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h24c2
  have h24qp := (hf24 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h23qp
  have h24j := (hf24 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h23j
  have h24rs := (hf24 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h23rs
  have h24d := (hf24 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h23d
  have h24qhc := (hf24 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h23qhc
  have h24ra := (hf24 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h23ra
  -- step 25: c3 := c2 ^ 1
  obtain ⟨e25, hs25, h25c3, hf25⟩ := semScalar_setExpr_run (y := "c3")
    (lower_xor_lit 1 (envReadU64_of_bound h24c2) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h24c2] at h25c3
  have h25qp := (hf25 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h24qp
  have h25j := (hf25 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h24j
  have h25rs := (hf25 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h24rs
  have h25d := (hf25 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h24d
  have h25qhc := (hf25 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h24qhc
  have h25ra := (hf25 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h24ra
  -- step 26: m3 := (~c3) + 1
  obtain ⟨e26, hs26, h26m3, hf26⟩ := semScalar_setExpr_run (y := "m3")
    (lower_notadd1 ones 1 (envReadU64_of_bound h25c3) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h25c3] at h26m3
  rw [notW] at h26m3
  have h26qp := (hf26 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h25qp
  have h26j := (hf26 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h25j
  have h26rs := (hf26 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h25rs
  have h26d := (hf26 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h25d
  have h26qhc := (hf26 "qhc" (notTmp_of_short "qhc" (by decide)) (by decide)).trans h25qhc
  have h26ra := (hf26 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h25ra
  have h26c3 := (hf26 "c3" (notTmp_of_short "c3" (by decide)) (by decide)).trans h25c3
  -- step 27: qout := qhc + c3
  obtain ⟨e27, hs27, h27qout, hf27⟩ := semScalar_setExpr_run (y := "qout")
    (lower_add_vv (envReadU64_of_bound h26qhc) (envReadU64_of_bound h26c3))
  simp only [SExpr.evalBV, envReader_of_bound h26qhc, envReader_of_bound h26c3] at h27qout
  have h27qp := (hf27 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h26qp
  have h27j := (hf27 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h26j
  have h27rs := (hf27 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h26rs
  have h27d := (hf27 "d" (notTmp_of_short "d" (by decide)) (by decide)).trans h26d
  have h27ra := (hf27 "ra" (notTmp_of_short "ra" (by decide)) (by decide)).trans h26ra
  have h27m3 := (hf27 "m3" (notTmp_of_short "m3" (by decide)) (by decide)).trans h26m3
  -- step 28: rout := ra - (m3 & d)
  obtain ⟨e28, hs28, h28rout, hf28⟩ := semScalar_setExpr_run (y := "rout")
    (lower_sub_and (envReadU64_of_bound h27ra) (envReadU64_of_bound h27m3)
      (envReadU64_of_bound h27d) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h27ra, envReader_of_bound h27m3,
    envReader_of_bound h27d] at h28rout
  have h28qp := (hf28 "qp" (notTmp_of_short "qp" (by decide)) (by decide)).trans h27qp
  have h28j := (hf28 "j" (notTmp_of_short "j" (by decide)) (by decide)).trans h27j
  have h28rs := (hf28 "rs" (notTmp_of_short "rs" (by decide)) (by decide)).trans h27rs
  have h28qout := (hf28 "qout" (notTmp_of_headNe rfl (by decide)) (by decide)).trans h27qout
  -- step 29: qp[j] := qout
  obtain ⟨e29, hs29, h29qp, hf29⟩ :=
    semScalar_arrStore (fw := 8 * NR) h28qp h28j h28qout
  rw [hjN] at h29qp
  have h29rs := (hf29 "rs" (by decide)).trans h28rs
  have h29rout := (hf29 "rout" (by decide)).trans h28rout
  -- step 30: qp[rs] := rout
  obtain ⟨e30, hs30, h30qp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h29qp h29rs h29rout
  rw [hrsN] at h30qp
  refine ⟨e30, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8, seqAll_step hs9,
      seqAll_step hs10, seqAll_step hs11, seqAll_step hs12, seqAll_step hs13,
      seqAll_step hs14, seqAll_step hs15, seqAll_step hs16, seqAll_step hs17,
      seqAll_step hs18, seqAll_step hs19, seqAll_step hs20, seqAll_step hs21,
      seqAll_step hs22, seqAll_step hs23, seqAll_step hs24, seqAll_step hs25,
      seqAll_step hs26, seqAll_step hs27, seqAll_step hs28, seqAll_step hs29]
    exact hs30
  · rw [h30qp]
    simp only [preinvFoldStep, preinvStep]
    rfl

/-! ## 8. The machine-level fold theorem -/

/-- **The runtime-trip `mpn_divrem_1` program denotes the reciprocal-step fold.**
    The compiled program's denotation at any valuation is `preinvFold` of the
    argument registers — the trip count read from `n`, the divisor `d`, the
    reciprocal `dinv` and the dividend array `up` threaded as invariants, the
    output array `qp` as the accumulator seed, descending from the top limb
    `n - 1`, the running remainder rider at cell `RS`. No front-compilation
    hypothesis remains.

    The fold is over `preinvFoldStep`, the Möller–Granlund reciprocal step the
    emitted body computes; identifying it with the exact Euclidean fold
    `divFold_val` is the undischarged `PreinvStepAgrees` and is not established
    here. -/
theorem divRtProg_fold (V : Ctxt.Valuation Gouter) :
    divRem1RtProgOpt.map (fun c => ComL.denote c V)
      = some (preinvFold (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V)
          ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V)) := by
  rw [divRem1RtProg_denote (update := divUpdate) divUpdate_eq V]
  refine congrArg some ?_
  have h64 := (nVar.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.sword 64, .sword 64, .sword 64, .memref NU]) vmBody "qp" divLimbBodyLowCT
    divLimbBody_covered
    (.cons (dVar.lookup V) (.cons (dinvVar.lookup V) (.cons (nVar.lookup V)
      (.cons (upVar.lookup V) .nil))))
    (fun arr tt => preinvFoldStep (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V)
      ((nVar.lookup V).toNat - 1) RS arr tt)
    (nVar.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        divLimbBody_run (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V) arr
          (nVar.lookup V) tt (by omega) htt
      exact ⟨divEnv (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V) arr
          (BitVec.ofNat 64 tt) (nVar.lookup V), env',
        consistentS_divEnv (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V) arr
          (BitVec.ofNat 64 tt) (nVar.lookup V),
        hrun, hrp⟩)
    divUpdate_eq (divInit.lookup V)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote
