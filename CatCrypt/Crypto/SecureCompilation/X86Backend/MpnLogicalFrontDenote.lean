/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The `mpn` bitwise-logical loop bodies against their source semantics

`MpnLogicalFrontEmit.logicRtProg_denote` states the emitted runtime-trip loop's
denotation as the `JLoopBodyN` fold of `update`, under the hypothesis
`frontLoopBodyJ … = some update`. This module supplies that `update`, runs each
source `LowCT` limb body symbolically through `semScalar` from the canonical
per-trip entry state, and identifies each trip with the word-model step
`logicFoldStep` — so the model-level cell theorems `andFold_cells` /
`iorFold_cells` / `xorFold_cells` read on the compiled programs' denotations.

The per-trip run is the finite per-command check: two `RArrLoad`s (the two
source limbs), one `RScalarSetExpr` combining them, one `RArrStore`, each stepped
by the waist lemmas of `Secp256k1PointOpFrameRoundTrip`. The body is parametric
over the combiner, so `logicLimbBody_run` takes the combiner's lowering-progress
and word-evaluation as hypotheses and each kernel instantiates them.

## Main results

* `logicLimbBody_run` — the per-trip `semScalar` run of the parametric body: from
  the canonical entry state at trip `t`, the body leaves `logicFoldStep f ap bp
  acc t` in `rp`, given the combiner's progress and evaluation.
* `andLimbBody_run` / `iorLimbBody_run` / `xorLimbBody_run` — the three
  instantiations at the GMP conjunction / disjunction / exclusive-or combiners.
* `andRtProg_fold` / `iorRtProg_fold` / `xorRtProg_fold` — each runtime-trip
  program's denotation is the `logicFold` word-model fold, with no remaining
  hypothesis.
* `andRtProg_val` / `iorRtProg_val` / `xorRtProg_val` — the machine-level cell
  theorems: the compiled programs' first `n` output cells are the elementwise
  `List.zipWith` of the two source arrays.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (sv seqAll cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once — the `by decide` on
the below-`4` name length is paid a single time per name — and referenced at the
freshness sites below, instead of re-deciding the string length at each site. -/

theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
theorem nt_x : ¬ isTmpName "x" := notTmp_of_short _ (by decide)
theorem nt_y : ¬ isTmpName "y" := notTmp_of_short _ (by decide)

/-! ## 1. Progress of the combiner `SExpr` shapes -/

/-- Progress of the conjunction of two variables. -/
theorem lower_and_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SAnd (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]; rfl

/-- Progress of the exclusive-or of two variables. -/
theorem lower_xor_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SXor (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]; rfl

/-- Progress of the synthesised disjunction of two variables — the emitted
    `orE` idiom `(x ^^^ y) ^^^ (x &&& y)`. -/
theorem lower_ior_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hxl : x.length < 4) (hyl : y.length < 4) :
    (semLowerSExpr env 0
      (.SXor (.SXor (.SVar x) (.SVar y)) (.SAnd (.SVar x) (.SVar y)))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), envReadU64_upd_ne (ne_tmp_of_short hyl 0),
    envReadU64_upd_ne (show tmpName 0 ≠ tmpName 1 by decide),
    envReadU64_upd_ne (show tmpName 2 ≠ tmpName 3 by decide),
    envReadU64_upd_self]
  rfl

/-! ## 2. The canonical per-trip entry state

The loop body shares the context `Gbody = [rp : .memref NL, idx : .sword 64,
ap : .memref NL, bp : .memref NL]` and `vmBody`, so all combiners share one entry
environment: the output array at `rp`, the trip index at `idx`, the two source
arrays at `ap` and `bp`. -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of a logical limb body at one trip. -/
def logicEnv (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) : SEnvScalar :=
  ((((emptyEnv.upd "bp" (t := .memref NL) bp).upd
      "ap" (t := .memref NL) ap).upd
      "idx" (t := .sword 64) iv).upd "rp" (t := .memref NL) acc)

theorem consistentS_logicEnv (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons ap (.cons bp .nil)))) (logicEnv ap bp acc iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    consistentS_empty "bp" (t := .memref NL) bp) "ap" (t := .memref NL) ap)
    "idx" (t := .sword 64) iv) "rp" (t := .memref NL) acc

theorem logicEnv_rp (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) :
    logicEnv ap bp acc iv "rp" = some ⟨.memref NL, acc⟩ := upd_self _ _ _

theorem logicEnv_idx (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) :
    logicEnv ap bp acc iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [logicEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem logicEnv_ap (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) :
    logicEnv ap bp acc iv "ap" = some ⟨.memref NL, ap⟩ := by
  rw [logicEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem logicEnv_bp (ap bp acc : Fin NL → BitVec 64) (iv : BitVec 64) :
    logicEnv ap bp acc iv "bp" = some ⟨.memref NL, bp⟩ := by
  rw [logicEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 3. The parametric per-trip run -/

/-- **The logical limb body computes one `logicFoldStep`.** From the canonical
    entry state at trip `t`, the source body's `semScalar` run terminates and
    leaves the word-model step's array in `rp`: cell `t` holds the combiner
    applied to the two source cells at index `t`. The per-command check of the
    four-command body, parametric over the combiner through its
    lowering-progress (`hlow`) and word-evaluation (`heval`). -/
theorem logicLimbBody_run (f : BitVec 64 → BitVec 64 → BitVec 64)
    (comb : SExpr → SExpr → SExpr)
    (hlow : ∀ {env : SEnvScalar} {wx wy : BitVec 64},
      envReadU64 env "x" = some wx → envReadU64 env "y" = some wy →
      (semLowerSExpr env 0 (comb (sv "x") (sv "y"))).isSome)
    (heval : ∀ β : String → BitVec 64,
      SExpr.evalBV β (comb (sv "x") (sv "y")) = f (β "x") (β "y"))
    (ap bp acc : Fin NL → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar (logicBodyLowCT comb) (logicEnv ap bp acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NL, logicFoldStep f ap bp acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by simp only [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : logicBodyLowCT comb = seqAll
    [ .RArrLoad ⟨"x", .TU64⟩ ⟨"ap", .TBytes (8 * NL)⟩ "idx"
    , .RArrLoad ⟨"y", .TU64⟩ ⟨"bp", .TBytes (8 * NL)⟩ "idx"
    , .RScalarSetExpr "z" (comb (sv "x") (sv "y"))
    , .RArrStore ⟨"rp", .TBytes (8 * NL)⟩ "idx" ⟨"z", .TU64⟩ ] := rfl
  -- step 1: x := ap[idx]
  obtain ⟨e1, hs1, h1x, hf1⟩ :=
    semScalar_arrLoad (dstN := "x") (tw := .TBytes (8 * NL)) (idxN := "idx")
      (logicEnv_ap ap bp acc iv) (logicEnv_idx ap bp acc iv)
  rw [hivN] at h1x
  have h1rp := (hf1 "rp" (by decide)).trans (logicEnv_rp ap bp acc iv)
  have h1bp := (hf1 "bp" (by decide)).trans (logicEnv_bp ap bp acc iv)
  have h1idx := (hf1 "idx" (by decide)).trans (logicEnv_idx ap bp acc iv)
  -- step 2: y := bp[idx]
  obtain ⟨e2, hs2, h2y, hf2⟩ :=
    semScalar_arrLoad (dstN := "y") (tw := .TBytes (8 * NL)) (idxN := "idx") h1bp h1idx
  rw [hivN] at h2y
  have h2rp := (hf2 "rp" (by decide)).trans h1rp
  have h2idx := (hf2 "idx" (by decide)).trans h1idx
  have h2x := (hf2 "x" (by decide)).trans h1x
  -- step 3: z := comb(x, y)
  obtain ⟨e3, hs3, h3z, hf3⟩ := semScalar_setExpr_run (y := "z")
    (hlow (envReadU64_of_bound h2x) (envReadU64_of_bound h2y))
  rw [heval (envReader e2), envReader_of_bound h2x, envReader_of_bound h2y] at h3z
  have h3rp := (hf3 "rp" (nt_rp) (by decide)).trans h2rp
  have h3idx := (hf3 "idx" (nt_idx) (by decide)).trans h2idx
  -- step 4: rp[idx] := z
  obtain ⟨e4, hs4, h4rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NL) h3rp h3idx h3z
  rw [hivN] at h4rp
  refine ⟨e4, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3]
    exact hs4
  · rw [h4rp]; rfl

/-! ## 4. The three combiner instantiations -/

/-- **The `mpn_and_n` limb body computes one conjunction `logicFoldStep`.** -/
theorem andLimbBody_run (ap bp acc : Fin NL → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar (logicBodyLowCT andSE) (logicEnv ap bp acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NL, logicFoldStep (fun x y => x &&& y) ap bp acc t⟩ :=
  logicLimbBody_run (fun x y => x &&& y) andSE
    (fun hx hy => lower_and_vv hx hy) (fun _ => rfl) ap bp acc t ht

/-- **The `mpn_xor_n` limb body computes one exclusive-or `logicFoldStep`.** -/
theorem xorLimbBody_run (ap bp acc : Fin NL → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar (logicBodyLowCT xorSE) (logicEnv ap bp acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NL, logicFoldStep (fun x y => x ^^^ y) ap bp acc t⟩ :=
  logicLimbBody_run (fun x y => x ^^^ y) xorSE
    (fun hx hy => lower_xor_vv hx hy) (fun _ => rfl) ap bp acc t ht

/-- **The `mpn_ior_n` limb body computes one disjunction `logicFoldStep`.** -/
theorem iorLimbBody_run (ap bp acc : Fin NL → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar (logicBodyLowCT iorSE) (logicEnv ap bp acc (BitVec.ofNat 64 t))
        = some env'
      ∧ env' "rp" = some ⟨.memref NL, logicFoldStep (fun x y => x ||| y) ap bp acc t⟩ :=
  logicLimbBody_run (fun x y => x ||| y) iorSE
    (fun hx hy => lower_ior_vv hx hy (by decide) (by decide))
    (fun β => iorSE_evalBV β (sv "x") (sv "y")) ap bp acc t ht

/-! ## 5. Coverage -/

/-- The `mpn_and_n` limb body is covered straight-line `LowCT`. -/
theorem andBody_coveredS : IsCoveredS (logicBodyLowCT andSE) :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _
          ⟨nt_x, nt_y⟩)
        (.rArrStore _ _ _)))

/-- The `mpn_and_n` limb body sits in the control-extended covered fragment. -/
theorem andBody_covered : IsCoveredSCtl (logicBodyLowCT andSE) :=
  .ofStraight andBody_coveredS

/-- The `mpn_xor_n` limb body is covered straight-line `LowCT`. -/
theorem xorBody_coveredS : IsCoveredS (logicBodyLowCT xorSE) :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _
          ⟨nt_x, nt_y⟩)
        (.rArrStore _ _ _)))

/-- The `mpn_xor_n` limb body sits in the control-extended covered fragment. -/
theorem xorBody_covered : IsCoveredSCtl (logicBodyLowCT xorSE) :=
  .ofStraight xorBody_coveredS

/-- The `mpn_ior_n` limb body is covered straight-line `LowCT`. -/
theorem iorBody_coveredS : IsCoveredS (logicBodyLowCT iorSE) :=
  .rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _
          ⟨⟨nt_x, nt_y⟩,
            ⟨nt_x, nt_y⟩⟩)
        (.rArrStore _ _ _)))

/-- The `mpn_ior_n` limb body sits in the control-extended covered fragment. -/
theorem iorBody_covered : IsCoveredSCtl (logicBodyLowCT iorSE) :=
  .ofStraight iorBody_coveredS

/-! ## 6. The front-compiled bodies -/

/-- The front accepts the `mpn_and_n` body. -/
theorem andFrontOk :
    (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT andSE)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_and_n` limb body. -/
def andUpdate (_ : Unit) : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NL)) :=
  (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT andSE)).get andFrontOk

/-- The equation `logicRtProg_denote` takes as its hypothesis for `mpn_and_n`. -/
theorem andUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT andSE)
      = some (andUpdate ()) :=
  (Option.some_get andFrontOk).symm

/-- The front accepts the `mpn_xor_n` body. -/
theorem xorFrontOk :
    (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT xorSE)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_xor_n` limb body. -/
def xorUpdate (_ : Unit) : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NL)) :=
  (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT xorSE)).get xorFrontOk

/-- The equation `logicRtProg_denote` takes as its hypothesis for `mpn_xor_n`. -/
theorem xorUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT xorSE)
      = some (xorUpdate ()) :=
  (Option.some_get xorFrontOk).symm

/-- The front accepts the `mpn_ior_n` body. -/
theorem iorFrontOk :
    (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT iorSE)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_ior_n` limb body. -/
def iorUpdate (_ : Unit) : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NL)) :=
  (frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT iorSE)).get iorFrontOk

/-- The equation `logicRtProg_denote` takes as its hypothesis for `mpn_ior_n`. -/
theorem iorUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT iorSE)
      = some (iorUpdate ()) :=
  (Option.some_get iorFrontOk).symm

/-! ## 7. The machine-level fold and cell theorems

The outer argument context is `Gouter = [n (RCX), bp (RDX), ap (RSI), rp (RDI)]`
(newest first). -/

/-- The first source-array argument `ap` (RSI). -/
abbrev apVar : Ctxt.Var Gouter AL := .there (.there .here)

/-- The second source-array argument `bp` (RDX). -/
abbrev bpVar : Ctxt.Var Gouter AL := .there .here

/-- **The runtime-trip `mpn_and_n` program denotes the elementwise fold.** The
    compiled program's denotation at any valuation is `logicFold` of the argument
    registers at the conjunction combiner. No front-compilation hypothesis
    remains. -/
theorem andRtProg_fold (V : Ctxt.Valuation Gouter) :
    (logicRtProgOpt andSE).map (fun c => ComL.denote c V)
      = some (logicFold (fun x y => x &&& y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V)) := by
  rw [logicRtProg_denote andSE andUpdate_eq V]
  congr 1
  have h64 := (logicCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NL)
    (invCTys := [.memref NL, .memref NL]) vmBody "rp" (logicBodyLowCT andSE)
    andBody_covered
    (.cons (apVar.lookup V) (.cons (bpVar.lookup V) .nil))
    (fun arr tt => logicFoldStep (fun x y => x &&& y) (apVar.lookup V) (bpVar.lookup V) arr tt)
    (logicCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        andLimbBody_run (apVar.lookup V) (bpVar.lookup V) arr tt (by omega)
      exact ⟨logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt), env',
        consistentS_logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    andUpdate_eq (logicInit.lookup V)

/-- **The runtime-trip `mpn_xor_n` program denotes the elementwise fold.** -/
theorem xorRtProg_fold (V : Ctxt.Valuation Gouter) :
    (logicRtProgOpt xorSE).map (fun c => ComL.denote c V)
      = some (logicFold (fun x y => x ^^^ y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V)) := by
  rw [logicRtProg_denote xorSE xorUpdate_eq V]
  congr 1
  have h64 := (logicCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NL)
    (invCTys := [.memref NL, .memref NL]) vmBody "rp" (logicBodyLowCT xorSE)
    xorBody_covered
    (.cons (apVar.lookup V) (.cons (bpVar.lookup V) .nil))
    (fun arr tt => logicFoldStep (fun x y => x ^^^ y) (apVar.lookup V) (bpVar.lookup V) arr tt)
    (logicCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        xorLimbBody_run (apVar.lookup V) (bpVar.lookup V) arr tt (by omega)
      exact ⟨logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt), env',
        consistentS_logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    xorUpdate_eq (logicInit.lookup V)

/-- **The runtime-trip `mpn_ior_n` program denotes the elementwise fold.** -/
theorem iorRtProg_fold (V : Ctxt.Valuation Gouter) :
    (logicRtProgOpt iorSE).map (fun c => ComL.denote c V)
      = some (logicFold (fun x y => x ||| y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V)) := by
  rw [logicRtProg_denote iorSE iorUpdate_eq V]
  congr 1
  have h64 := (logicCount.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NL)
    (invCTys := [.memref NL, .memref NL]) vmBody "rp" (logicBodyLowCT iorSE)
    iorBody_covered
    (.cons (apVar.lookup V) (.cons (bpVar.lookup V) .nil))
    (fun arr tt => logicFoldStep (fun x y => x ||| y) (apVar.lookup V) (bpVar.lookup V) arr tt)
    (logicCount.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        iorLimbBody_run (apVar.lookup V) (bpVar.lookup V) arr tt (by omega)
      exact ⟨logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt), env',
        consistentS_logicEnv (apVar.lookup V) (bpVar.lookup V) arr (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    iorUpdate_eq (logicInit.lookup V)

/-- **The compiled `mpn_and_n` computes the elementwise conjunction.** For a trip
    count within the model's output array, the compiled program's first `n`
    output cells are the elementwise `List.zipWith` conjunction of the two source
    arrays — `andFold_cells` read on the machine-level denotation. -/
theorem andRtProg_val (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL) :
    ∃ out : Fin NL → BitVec 64,
      (logicRtProgOpt andSE).map (fun c => ComL.denote c V) = some out ∧
        cells out (logicCount.lookup V).toNat
          = List.zipWith (fun x y => x &&& y)
              (cells (apVar.lookup V) (logicCount.lookup V).toNat)
              (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  ⟨_, andRtProg_fold V,
   andFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
     (logicCount.lookup V).toNat hn⟩

/-- **The compiled `mpn_xor_n` computes the elementwise exclusive-or.** -/
theorem xorRtProg_val (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL) :
    ∃ out : Fin NL → BitVec 64,
      (logicRtProgOpt xorSE).map (fun c => ComL.denote c V) = some out ∧
        cells out (logicCount.lookup V).toNat
          = List.zipWith (fun x y => x ^^^ y)
              (cells (apVar.lookup V) (logicCount.lookup V).toNat)
              (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  ⟨_, xorRtProg_fold V,
   xorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
     (logicCount.lookup V).toNat hn⟩

/-- **The compiled `mpn_ior_n` computes the elementwise disjunction.** -/
theorem iorRtProg_val (V : Ctxt.Valuation Gouter) (hn : (logicCount.lookup V).toNat ≤ NL) :
    ∃ out : Fin NL → BitVec 64,
      (logicRtProgOpt iorSE).map (fun c => ComL.denote c V) = some out ∧
        cells out (logicCount.lookup V).toNat
          = List.zipWith (fun x y => x ||| y)
              (cells (apVar.lookup V) (logicCount.lookup V).toNat)
              (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  ⟨_, iorRtProg_fold V,
   iorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
     (logicCount.lookup V).toNat hn⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
