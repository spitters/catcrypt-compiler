/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyNestedStepC
public import CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref

/-!
# The nested `mpn_mul_basecase` loop body against its source semantics

`MpnMulBasecaseFrontEmit.bcProg_denote` states the emitted nested runtime-trip
program's denotation as the `JLoopBodyN.nestedDenote` double fold of the two
front bodies, under the hypotheses that the front compiles `cntBodyLowCT` to
`innerCount` and `rowBodyLowCT` to `innerUpdate`. This module supplies those two
front-success facts structurally, runs the source `LowCT` row body symbolically
through `semScalar` from the canonical per-trip entry state, identifies each
inner trip with the word-model step `bcStep`, and reads the schoolbook product
contract `bcFold_val_zero` on the compiled program's denotation.

The nested per-trip run is the finite per-command check of the twenty-five
`rowBodyLowCT` commands, stepped by the waist lemmas of
`Secp256k1PointOpFrameRoundTrip`, with the outer row index prepended to the
loop-body invariants (`invCTys := .sword 64 :: Ginv`). The three `bSltu`
carry/mask idioms it needs are `ltu_chain` (the emitted xor/and idiom is
`bSltu`) and `bcSel_eq` (the branch-free flush mask reads `bcLimb`); the one
word identity is `hiU_eq` (the `SMulHiU` evaluator is `mulHiW`).

## Main results

* `rowBody_coveredS` / `rowBody_covered` — the row body is covered straight-line
  `LowCT`.
* `cntFrontOk` / `bcFrontOk` — the inner-count and row bodies are accepted by the
  rolled-loop front, proved structurally (no `maxRecDepth` reduction).
* `cntBody_run` / `bcRowBody_run` — the per-trip `semScalar` runs: the count body
  leaves `un + 1` in `cnt`, and the row body leaves `bcStep` in `rp`.
* `bcRtProg_fold` — the nested program's denotation is the `bcFold` schoolbook
  double fold, with no remaining front-compilation hypothesis.
* `bcRtProg_val` — the machine-level value theorem: the compiled program's output
  cells recombine via `bignumVal` to `up[0..un) * vp[0..vn)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredS IsCoveredSCtl srcClean isTmpName
   envReadU64 envReader semLowerSExpr binNode consistentS_empty)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (consistentS_bind)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyNestedStepC (nestedDenote_foldl)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys TransTotal SrcTys VmApprox BoundAt boundAt_bind_self boundAt_bind_of_ne
   frontLoopBodyJ_total)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (upd_ne upd_self envReadU64_of_bound envReader_of_bound envReadU64_upd_ne
   envReadU64_upd_self semScalar_arrLoad semScalar_arrStore semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Ascent (notTmp_of_short)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds ones notE orE cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short emptyEnv hiU_eq ltu_chain seqAll_step semScalar_seqAll_cons
   lower_mul_vv lower_hiu_vv lower_add_vv lower_add_lit lower_cq lower_cr lower_orshr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal (transSteps_seqAll)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 0. Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once here — the `by decide`
on the below-`4` name length is paid a single time per name — and referenced by
the frame-transport steps below, instead of re-deciding the string length at each
of the ~180 transport sites. -/

theorem nt_a : ¬ isTmpName "a" := notTmp_of_short _ (by decide)
theorem nt_a0 : ¬ isTmpName "a0" := notTmp_of_short _ (by decide)
theorem nt_cnt : ¬ isTmpName "cnt" := notTmp_of_short _ (by decide)
theorem nt_cy : ¬ isTmpName "cy" := notTmp_of_short _ (by decide)
theorem nt_hc : ¬ isTmpName "hc" := notTmp_of_short _ (by decide)
theorem nt_hi : ¬ isTmpName "hi" := notTmp_of_short _ (by decide)
theorem nt_jd : ¬ isTmpName "jd" := notTmp_of_short _ (by decide)
theorem nt_k1 : ¬ isTmpName "k1" := notTmp_of_short _ (by decide)
theorem nt_k1q : ¬ isTmpName "k1q" := notTmp_of_short _ (by decide)
theorem nt_k1r : ¬ isTmpName "k1r" := notTmp_of_short _ (by decide)
theorem nt_k2 : ¬ isTmpName "k2" := notTmp_of_short _ (by decide)
theorem nt_k2q : ¬ isTmpName "k2q" := notTmp_of_short _ (by decide)
theorem nt_k2r : ¬ isTmpName "k2r" := notTmp_of_short _ (by decide)
theorem nt_kb : ¬ isTmpName "kb" := notTmp_of_short _ (by decide)
theorem nt_kbq : ¬ isTmpName "kbq" := notTmp_of_short _ (by decide)
theorem nt_kbr : ¬ isTmpName "kbr" := notTmp_of_short _ (by decide)
theorem nt_lo : ¬ isTmpName "lo" := notTmp_of_short _ (by decide)
theorem nt_msk : ¬ isTmpName "msk" := notTmp_of_short _ (by decide)
theorem nt_nc : ¬ isTmpName "nc" := notTmp_of_short _ (by decide)
theorem nt_pi : ¬ isTmpName "pi" := notTmp_of_short _ (by decide)
theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
theorem nt_rr : ¬ isTmpName "rr" := notTmp_of_short _ (by decide)
theorem nt_s1 : ¬ isTmpName "s1" := notTmp_of_short _ (by decide)
theorem nt_s2 : ¬ isTmpName "s2" := notTmp_of_short _ (by decide)
theorem nt_t : ¬ isTmpName "t" := notTmp_of_short _ (by decide)
theorem nt_tm : ¬ isTmpName "tm" := notTmp_of_short _ (by decide)
theorem nt_un : ¬ isTmpName "un" := notTmp_of_short _ (by decide)
theorem nt_up : ¬ isTmpName "up" := notTmp_of_short _ (by decide)
theorem nt_vn : ¬ isTmpName "vn" := notTmp_of_short _ (by decide)
theorem nt_vp : ¬ isTmpName "vp" := notTmp_of_short _ (by decide)
theorem nt_vv : ¬ isTmpName "vv" := notTmp_of_short _ (by decide)

/-! ## 1. New `SExpr` lowering-progress shapes -/

/-- Progress of `0 - x` for a bound short-named word. -/
theorem lower_sub0_var {env : SEnvScalar} {x : String} {wx : BitVec 64}
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SSub (.SLit 0) (.SVar x))).isSome := by
  simp only [semLowerSExpr, binNode, envReadU64_upd_self,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), hx]
  rfl

/-- Progress of `x & y` for two bound words. -/
theorem lower_and_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SAnd (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

/-- Progress of `(x + y) + z` for three bound words, `z` short. -/
theorem lower_add_add {env : SEnvScalar} {x y z : String} {wx wy wz : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hz : envReadU64 env z = some wz) (hzl : z.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SAdd (.SVar x) (.SVar y)) (.SVar z))).isSome := by
  simp only [semLowerSExpr, hx, hy, hz, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hzl 0), envReadU64_upd_self]
  rfl

/-! ## 2. The row body as an explicit command list -/

/-- The twenty-five commands of the row body, fully expanded (`ltuCmds` / `notE`
    / `orE` unfolded), the shape both the coverage proof and the per-trip run
    read off. -/
def rowBodyList : List LowCT :=
  [ .RScalarSetExpr "kbq" (.SAnd (notE (sv "t")) (sv "un"))
  , .RScalarSetExpr "kbr" (.SAnd (notE (.SXor (sv "t") (sv "un"))) (.SSub (sv "t") (sv "un")))
  , .RScalarSetExpr "kb" (.SShr (orE (.SVar "kbq") (.SVar "kbr")) (.SLit 63))
  , .RScalarSetExpr "msk" (.SSub (.SLit 0) (sv "kb"))
  , .RScalarSetExpr "tm" (.SAnd (sv "t") (sv "msk"))
  , .RArrLoad ⟨"a0", .TU64⟩ upLoc "tm"
  , .RScalarSetExpr "a" (.SAnd (sv "a0") (sv "msk"))
  , .RArrLoad ⟨"vv", .TU64⟩ vpLoc "jd"
  , .RScalarSetExpr "lo" (.SMul (sv "a") (sv "vv"))
  , .RScalarSetExpr "hi" (.SMulHiU (sv "a") (sv "vv"))
  , .RScalarSetExpr "nc" (.SAdd (sv "un") (sv "vn"))
  , .RArrLoad ⟨"cy", .TU64⟩ rpLoc "nc"
  , .RScalarSetExpr "s1" (.SAdd (sv "lo") (sv "cy"))
  , .RScalarSetExpr "k1q" (.SAnd (notE (sv "s1")) (sv "lo"))
  , .RScalarSetExpr "k1r" (.SAnd (notE (.SXor (sv "s1") (sv "lo"))) (.SSub (sv "s1") (sv "lo")))
  , .RScalarSetExpr "k1" (.SShr (orE (.SVar "k1q") (.SVar "k1r")) (.SLit 63))
  , .RScalarSetExpr "pi" (.SAdd (sv "jd") (sv "t"))
  , .RArrLoad ⟨"rr", .TU64⟩ rpLoc "pi"
  , .RScalarSetExpr "s2" (.SAdd (sv "s1") (sv "rr"))
  , .RScalarSetExpr "k2q" (.SAnd (notE (sv "s2")) (sv "s1"))
  , .RScalarSetExpr "k2r" (.SAnd (notE (.SXor (sv "s2") (sv "s1"))) (.SSub (sv "s2") (sv "s1")))
  , .RScalarSetExpr "k2" (.SShr (orE (.SVar "k2q") (.SVar "k2r")) (.SLit 63))
  , .RScalarSetExpr "hc" (.SAdd (.SAdd (sv "hi") (sv "k1")) (sv "k2"))
  , .RArrStore rpLoc "pi" ⟨"s2", .TU64⟩
  , .RArrStore rpLoc "nc" ⟨"hc", .TU64⟩ ]

theorem rowBody_eq : rowBodyLowCT = seqAll rowBodyList := rfl

/-- `seqAll` of a list of covered commands is covered. -/
theorem coveredS_seqAll : ∀ {l : List LowCT}, (∀ c ∈ l, IsCoveredS c) → IsCoveredS (seqAll l)
  | [], _ => .rSkip
  | [_c], h => h _c (by simp)
  | _c :: _d :: _cs, h =>
      .rSeq (h _c (by simp)) (coveredS_seqAll (fun x hx => h x (List.mem_cons_of_mem _c hx)))

/-- The row body sits in the covered straight-line fragment. -/
theorem rowBody_coveredS : IsCoveredS rowBodyLowCT := by
  rw [rowBody_eq]
  apply coveredS_seqAll
  intro c hc
  fin_cases hc <;>
    first
    | exact .rArrLoad _ _ _
    | exact .rArrStore _ _ _
    | (refine .rScalarSetExpr _ _ ?_;
       simp only [srcClean, sv, notE, orE, ones];
       repeat' first
         | apply And.intro
         | exact notTmp_of_short _ (by decide)
         | decide)

/-- The row body sits in the control-extended covered fragment. -/
theorem rowBody_covered : IsCoveredSCtl rowBodyLowCT := .ofStraight rowBody_coveredS

/-! ## 3. Front-success gates (structural) -/

/-- The reads-bound builder for the widening-high multiply node. -/
theorem readsFrom_mulhiu {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SMulHiU a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-- The three-memref name map: `rp` at the output type, `up` / `vp` at the two
    operand types. -/
def bcMem : String → Option CryptoTy := fun x =>
  if x = "rp" then some (.memref NR)
  else if x = "up" then some (.memref NU)
  else if x = "vp" then some (.memref NV)
  else none

theorem bcMem_rp : bcMem "rp" = some (.memref NR) := by decide
theorem bcMem_up : bcMem "up" = some (.memref NU) := by decide
theorem bcMem_vp : bcMem "vp" = some (.memref NV) := by decide

/-- The row-body entry word set: the inner index `t`, outer index `jd`, and the
    two runtime limb counts `un` / `vn`. -/
abbrev bcB0 : String → Prop := fun y => ((y = "t" ∨ y = "un") ∨ y = "jd") ∨ y = "vn"

theorem bcMem_notTmp : ∀ x t, bcMem x = some t → ¬ isTmpName x := by
  intro x t hx
  by_cases hrp : x = "rp"
  · exact hrp ▸ nt_rp
  · by_cases hup : x = "up"
    · exact hup ▸ nt_up
    · by_cases hvp : x = "vp"
      · exact hvp ▸ nt_vp
      · simp [bcMem, hrp, hup, hvp] at hx

/-- The three-command `ltuCmds` block emits reads-bound commands from a bound
    operand set (the `bcMem` instance of the `mpn_cmp` helper). -/
theorem bc_ltuCmds {B W : String → Prop} {l : List LowCT} {dst : String}
    {x y : SExpr} (h : TransFromM bcMem B W l)
    (hq : ¬ isTmpName (dst ++ "q")) (hqm : bcMem (dst ++ "q") = none)
    (hr : ¬ isTmpName (dst ++ "r")) (hrm : bcMem (dst ++ "r") = none)
    (hd : ¬ isTmpName dst) (hdm : bcMem dst = none)
    (hx : ReadsFrom W x) (hy : ReadsFrom W y) :
    TransFromM bcMem B (fun z => ((W z ∨ z = dst ++ "q") ∨ z = dst ++ "r") ∨ z = dst)
      (l ++ ltuCmds dst x y) := by
  have hones : ones < 2 ^ 64 := by decide
  unfold ltuCmds
  refine transFromM_snoc3 h hq hqm hr hrm hd hdm ?_ ?_ ?_
  · exact readsFrom_and (readsFrom_xor hx (readsFrom_lit hones)) hy
  · exact readsFrom_and
      (readsFrom_xor (readsFrom_xor (readsFrom_mono hx (fun _ h => Or.inl h))
        (readsFrom_mono hy (fun _ h => Or.inl h))) (readsFrom_lit hones))
      (readsFrom_sub (readsFrom_mono hx (fun _ h => Or.inl h))
        (readsFrom_mono hy (fun _ h => Or.inl h)))
  · exact readsFrom_shr
      (readsFrom_xor
        (readsFrom_xor (readsFrom_var hq (Or.inl (Or.inr rfl)))
          (readsFrom_var hr (Or.inr rfl)))
        (readsFrom_and (readsFrom_var hq (Or.inl (Or.inr rfl)))
          (readsFrom_var hr (Or.inr rfl))))
      (readsFrom_lit (by decide : (63 : Nat) < 2 ^ 64))

theorem bcB0_srcSet : SrcSet bcB0 := by
  rintro x (((rfl | rfl) | rfl) | rfl) <;> exact notTmp_of_short _ (by decide)

theorem bcB0_disjoint : ∀ x, bcB0 x → bcMem x = none := by
  rintro x (((rfl | rfl) | rfl) | rfl) <;> decide

theorem vmApprox_bc : VmApprox (nameTysM bcMem bcB0) vmBody := by
  intro x t hx
  by_cases hrp : x = "rp"
  · subst hrp
    rw [nameTysM_mem bcMem_rp] at hx
    obtain rfl := (Option.some.inj hx).symm
    exact boundAt_bind_self _ "rp" (.memref NR)
  · by_cases hup : x = "up"
    · subst hup
      rw [nameTysM_mem bcMem_up] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
        (boundAt_bind_of_ne "t" (.sword 64) (by decide)
          (boundAt_bind_of_ne "jd" (.sword 64) (by decide)
            (boundAt_bind_self _ "up" (.memref NU))))
    · by_cases hvp : x = "vp"
      · subst hvp
        rw [nameTysM_mem bcMem_vp] at hx
        obtain rfl := (Option.some.inj hx).symm
        exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
          (boundAt_bind_of_ne "t" (.sword 64) (by decide)
            (boundAt_bind_of_ne "jd" (.sword 64) (by decide)
              (boundAt_bind_of_ne "up" (.memref NU) (by decide)
                (boundAt_bind_self _ "vp" (.memref NV)))))
      · by_cases ht : x = "t"
        · subst ht
          rw [nameTysM_word (by decide : bcMem "t" = none)
            (show bcB0 "t" from Or.inl (Or.inl (Or.inl rfl)))] at hx
          obtain rfl := (Option.some.inj hx).symm
          exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
            (boundAt_bind_self _ "t" (.sword 64))
        · by_cases hun : x = "un"
          · subst hun
            rw [nameTysM_word (by decide : bcMem "un" = none)
              (show bcB0 "un" from Or.inl (Or.inl (Or.inr rfl)))] at hx
            obtain rfl := (Option.some.inj hx).symm
            exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
              (boundAt_bind_of_ne "t" (.sword 64) (by decide)
                (boundAt_bind_of_ne "jd" (.sword 64) (by decide)
                  (boundAt_bind_of_ne "up" (.memref NU) (by decide)
                    (boundAt_bind_of_ne "vp" (.memref NV) (by decide)
                      (boundAt_bind_self _ "un" (.sword 64))))))
          · by_cases hjd : x = "jd"
            · subst hjd
              rw [nameTysM_word (by decide : bcMem "jd" = none)
                (show bcB0 "jd" from Or.inl (Or.inr rfl))] at hx
              obtain rfl := (Option.some.inj hx).symm
              exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
                (boundAt_bind_of_ne "t" (.sword 64) (by decide)
                  (boundAt_bind_self _ "jd" (.sword 64)))
            · by_cases hvn : x = "vn"
              · subst hvn
                rw [nameTysM_word (by decide : bcMem "vn" = none)
                  (show bcB0 "vn" from Or.inr rfl)] at hx
                obtain rfl := (Option.some.inj hx).symm
                exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
                  (boundAt_bind_of_ne "t" (.sword 64) (by decide)
                    (boundAt_bind_of_ne "jd" (.sword 64) (by decide)
                      (boundAt_bind_of_ne "up" (.memref NU) (by decide)
                        (boundAt_bind_of_ne "vp" (.memref NV) (by decide)
                          (boundAt_bind_of_ne "un" (.sword 64) (by decide)
                            (boundAt_bind_self _ "vn" (.sword 64)))))))
              · rw [nameTysM_none (by simp [bcMem, hrp, hup, hvp])
                  (by rintro (((rfl | rfl) | rfl) | rfl) <;> simp_all)] at hx
                simp at hx

/-- The rolled-loop front accepts the runtime-trip `mpn_mul_basecase` row body,
    proved structurally (no `maxRecDepth` reduction of the command list). -/
theorem bcFrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" rowBodyLowCT).isSome := by
  have hlit0 : (0 : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromM bcMem bcB0 bcB0 [] := transFromM_nil bcB0
  have h1 := bc_ltuCmds (dst := "kb") h0
    (nt_kbq) (by decide)
    (nt_kbr) (by decide)
    (nt_kb) (by decide)
    (readsFrom_var (nt_t) (by decide))
    (readsFrom_var (nt_un) (by decide))
  have h2 := transFromM_snoc (x := "msk") h1 (nt_msk) (by decide)
    (readsFrom_sub (readsFrom_lit hlit0)
      (readsFrom_var (nt_kb) (by decide)))
  have h3 := transFromM_snoc (x := "tm") h2 (nt_tm) (by decide)
    (readsFrom_and (readsFrom_var (nt_t) (by decide))
      (readsFrom_var (nt_msk) (by decide)))
  have h4 := transFromM_snocLoad (d := "a0") (ix := "tm") (mty := .TBytes (8 * NU)) h3
    (nt_a0) (by decide) bcMem_up (by decide)
  have h5 := transFromM_snoc (x := "a") h4 (nt_a) (by decide)
    (readsFrom_and (readsFrom_var (nt_a0) (by decide))
      (readsFrom_var (nt_msk) (by decide)))
  have h6 := transFromM_snocLoad (d := "vv") (ix := "jd") (mty := .TBytes (8 * NV)) h5
    (nt_vv) (by decide) bcMem_vp (by decide)
  have h7 := transFromM_snoc (x := "lo") h6 (nt_lo) (by decide)
    (readsFrom_mul (readsFrom_var (nt_a) (by decide))
      (readsFrom_var (nt_vv) (by decide)))
  have h8 := transFromM_snoc (x := "hi") h7 (nt_hi) (by decide)
    (readsFrom_mulhiu (readsFrom_var (nt_a) (by decide))
      (readsFrom_var (nt_vv) (by decide)))
  have h9 := transFromM_snoc (x := "nc") h8 (nt_nc) (by decide)
    (readsFrom_add (readsFrom_var (nt_un) (by decide))
      (readsFrom_var (nt_vn) (by decide)))
  have h10 := transFromM_snocLoad (d := "cy") (ix := "nc") (mty := .TBytes (8 * NR)) h9
    (nt_cy) (by decide) bcMem_rp (by decide)
  have h11 := transFromM_snoc (x := "s1") h10 (nt_s1) (by decide)
    (readsFrom_add (readsFrom_var (nt_lo) (by decide))
      (readsFrom_var (nt_cy) (by decide)))
  have h12 := bc_ltuCmds (dst := "k1") h11
    (nt_k1q) (by decide)
    (nt_k1r) (by decide)
    (nt_k1) (by decide)
    (readsFrom_var (nt_s1) (by decide))
    (readsFrom_var (nt_lo) (by decide))
  have h13 := transFromM_snoc (x := "pi") h12 (nt_pi) (by decide)
    (readsFrom_add (readsFrom_var (nt_jd) (by decide))
      (readsFrom_var (nt_t) (by decide)))
  have h14 := transFromM_snocLoad (d := "rr") (ix := "pi") (mty := .TBytes (8 * NR)) h13
    (nt_rr) (by decide) bcMem_rp (by decide)
  have h15 := transFromM_snoc (x := "s2") h14 (nt_s2) (by decide)
    (readsFrom_add (readsFrom_var (nt_s1) (by decide))
      (readsFrom_var (nt_rr) (by decide)))
  have h16 := bc_ltuCmds (dst := "k2") h15
    (nt_k2q) (by decide)
    (nt_k2r) (by decide)
    (nt_k2) (by decide)
    (readsFrom_var (nt_s2) (by decide))
    (readsFrom_var (nt_s1) (by decide))
  have h17 := transFromM_snoc (x := "hc") h16 (nt_hc) (by decide)
    (readsFrom_add
      (readsFrom_add (readsFrom_var (nt_hi) (by decide))
        (readsFrom_var (nt_k1) (by decide)))
      (readsFrom_var (nt_k2) (by decide)))
  have h18 := transFromM_snocStore (m := "rp") (ix := "pi") (s := "s2")
    (mty := .TBytes (8 * NR)) h17 (nt_rp) bcMem_rp rfl
    (by decide) (by decide)
  have h19 := transFromM_snocStore (m := "rp") (ix := "nc") (s := "hc")
    (mty := .TBytes (8 * NR)) h18 (nt_rp) bcMem_rp rfl
    (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ := h19 bcB0 bcB0_srcSet bcB0_disjoint (fun _ h => h)
  have hT : TransTotal (nameTysM bcMem bcB0) rowBodyLowCT (nameTysM bcMem D) :=
    transSteps_seqAll hts
  exact frontLoopBodyJ_total vmBody "rp" rowBodyLowCT hT
    (srcTys_nameTysM bcMem_notTmp bcB0_srcSet) vmApprox_bc (nameTysM_mem bcMem_rp)

/-- The name map for the inner-count body: no memrefs, only the word `un`. -/
def cntMem : String → Option CryptoTy := fun _ => none

abbrev cntB0 : String → Prop := fun y => y = "un"

theorem cntB0_srcSet : SrcSet cntB0 := by
  rintro x rfl; exact nt_un

theorem vmApprox_cnt : VmApprox (nameTysM cntMem cntB0) vmCount := by
  intro x t hx
  by_cases hun : x = "un"
  · subst hun
    rw [nameTysM_word (by decide : cntMem "un" = none) (show cntB0 "un" from rfl)] at hx
    obtain rfl := (Option.some.inj hx).symm
    exact boundAt_bind_of_ne "jd" (.sword 64) (by decide)
      (boundAt_bind_of_ne "up" (.memref NU) (by decide)
        (boundAt_bind_of_ne "vp" (.memref NV) (by decide)
          (boundAt_bind_self _ "un" (.sword 64))))
  · rw [nameTysM_none (by simp [cntMem]) (by exact hun)] at hx
    simp at hx

/-- The rolled-loop front accepts the inner-count body. -/
theorem cntFrontOk :
    (frontLoopBodyJ (accCTy := .sword 64) vmCount "cnt" cntBodyLowCT).isSome := by
  have hrd : ReadsFrom cntB0 (.SAdd (sv "un") (.SLit 1)) :=
    readsFrom_add (readsFrom_var (nt_un) rfl)
      (readsFrom_lit (by decide))
  have hT : TransTotal (nameTysM cntMem cntB0) cntBodyLowCT
      ((nameTysM cntMem cntB0).upd "cnt" (.sword 64)) :=
    TransTotal.rScalarSetExpr "cnt" _ (nt_cnt) hrd.1
      (fun y hy => nameTysM_word (by simp [cntMem]) (hrd.2 y hy))
  refine frontLoopBodyJ_total vmCount "cnt" cntBodyLowCT hT
    (srcTys_nameTysM (by intro x t h; simp [cntMem] at h) cntB0_srcSet) vmApprox_cnt ?_
  rw [nameTysM_upd_word (by simp [cntMem])]
  exact nameTysM_word (by simp [cntMem]) (Or.inr rfl)

/-- The front-compiled row body (the `bcProg_denote` hypothesis). -/
def bcRowUpdate : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" rowBodyLowCT).get bcFrontOk

theorem bcRowUpdate_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" rowBodyLowCT = some bcRowUpdate :=
  (Option.some_get bcFrontOk).symm

/-- The front-compiled inner-count body. -/
def bcCntUpdate : Com jasminDialect (mapCtx Gcount) (mapTy (CryptoTy.sword 64)) :=
  (frontLoopBodyJ (accCTy := .sword 64) vmCount "cnt" cntBodyLowCT).get cntFrontOk

theorem bcCntUpdate_eq :
    frontLoopBodyJ (accCTy := .sword 64) vmCount "cnt" cntBodyLowCT = some bcCntUpdate :=
  (Option.some_get cntFrontOk).symm

/-! ## 4. Scope helpers -/

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_add_toNat {a b : Nat} (h : a + b < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
  have ha : a < 2 ^ 64 := by omega
  have hb : b < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  omega

theorem bv_add_toNat (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

/-! ## 5. The canonical per-trip entry states -/

/-- The canonical entry environment of the row body at one trip. -/
def bcRowEnv (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) : SEnvScalar :=
  ((((((emptyEnv.upd "vn" (t := .sword 64) vn).upd
      "un" (t := .sword 64) un).upd
      "vp" (t := .memref NV) vp).upd
      "up" (t := .memref NU) up).upd
      "jd" (t := .sword 64) jv).upd
      "t" (t := .sword 64) tv).upd "rp" (t := .memref NR) acc

theorem consistentS_bcRowEnv (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons tv (.cons jv (.cons up (.cons vp (.cons un (.cons vn .nil)))))))
      (bcRowEnv acc tv jv up vp un vn) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind (consistentS_bind consistentS_empty "vn" (t := .sword 64) vn)
      "un" (t := .sword 64) un) "vp" (t := .memref NV) vp) "up" (t := .memref NU) up)
    "jd" (t := .sword 64) jv) "t" (t := .sword 64) tv) "rp" (t := .memref NR) acc

theorem bcRowEnv_rp (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "rp" = some ⟨.memref NR, acc⟩ := upd_self _ _ _

theorem bcRowEnv_t (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "t" = some ⟨.sword 64, tv⟩ := by
  rw [bcRowEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem bcRowEnv_jd (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "jd" = some ⟨.sword 64, jv⟩ := by
  rw [bcRowEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem bcRowEnv_up (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "up" = some ⟨.memref NU, up⟩ := by
  rw [bcRowEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

theorem bcRowEnv_vp (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "vp" = some ⟨.memref NV, vp⟩ := by
  rw [bcRowEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

theorem bcRowEnv_un (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "un" = some ⟨.sword 64, un⟩ := by
  rw [bcRowEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide),
    upd_ne (by decide)]
  exact upd_self _ _ _

theorem bcRowEnv_vn (acc : Fin NR → BitVec 64) (tv jv : BitVec 64)
    (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64) (un vn : BitVec 64) :
    bcRowEnv acc tv jv up vp un vn "vn" = some ⟨.sword 64, vn⟩ := by
  rw [bcRowEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide), upd_ne (by decide),
    upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 6. The per-trip runs -/

/-- **The row body computes one `bcStep`.** From the canonical entry state at row
    `jd`, inner trip `t`, the source body's `semScalar` run terminates and leaves
    the word-model step's array in `rp`. -/
theorem bcRowBody_run (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un vn : BitVec 64) (acc : Fin NR → BitVec 64) (jd t : Nat)
    (ht : t < 2 ^ 64) (hj : jd < 2 ^ 64) (hpi : jd + t < 2 ^ 64)
    (hnc : un.toNat + vn.toNat < 2 ^ 64) :
    ∃ env',
      semScalar rowBodyLowCT
          (bcRowEnv acc (BitVec.ofNat 64 t) (BitVec.ofNat 64 jd) up vp un vn) = some env'
        ∧ env' "rp" = some ⟨.memref NR,
            bcStep up vp un.toNat (un.toNat + vn.toNat) jd acc t⟩ := by
  set tv : BitVec 64 := BitVec.ofNat 64 t with htvdef
  set jv : BitVec 64 := BitVec.ofNat 64 jd with hjvdef
  have htN : tv.toNat = t := by rw [htvdef]; exact ofNat_toNat ht
  have hjN : jv.toNat = jd := by rw [hjvdef]; exact ofNat_toNat hj
  have hncN : (un + vn).toNat = un.toNat + vn.toNat := bv_add_toNat un vn hnc
  have hpiN : (jv + tv).toNat = jd + t := by
    rw [hjvdef, htvdef]; exact ofNat_add_toNat hpi
  have ha_bcSel :
      memGetDyn up (tv &&& (BitVec.ofNat 64 0 - bSltu tv un)).toNat
          &&& (BitVec.ofNat 64 0 - bSltu tv un)
        = bcLimb up un.toNat t := by
    have h0eq : (BitVec.ofNat 64 0 : BitVec 64) = 0 := rfl
    rw [h0eq, show
        memGetDyn up (tv &&& (0 - bSltu tv un)).toNat &&& (0 - bSltu tv un)
          = bcSel up un tv from rfl, bcSel_eq, htN]
    rfl
  -- entry reads
  have h0_rp := bcRowEnv_rp acc tv jv up vp un vn
  have h0_t := bcRowEnv_t acc tv jv up vp un vn
  have h0_jd := bcRowEnv_jd acc tv jv up vp un vn
  have h0_up := bcRowEnv_up acc tv jv up vp un vn
  have h0_vp := bcRowEnv_vp acc tv jv up vp un vn
  have h0_un := bcRowEnv_un acc tv jv up vp un vn
  have h0_vn := bcRowEnv_vn acc tv jv up vp un vn
  -- step 1: kbq
  obtain ⟨e1, hs1, h1_kbq, hf1⟩ := semScalar_setExpr_run (y := "kbq")
    (lower_cq ones (envReadU64_of_bound h0_t) (envReadU64_of_bound h0_un) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h0_t, envReader_of_bound h0_un] at h1_kbq
  have h1_rp := (hf1 "rp" nt_rp (by decide)).trans h0_rp
  have h1_t := (hf1 "t" nt_t (by decide)).trans h0_t
  have h1_jd := (hf1 "jd" nt_jd (by decide)).trans h0_jd
  have h1_up := (hf1 "up" nt_up (by decide)).trans h0_up
  have h1_vp := (hf1 "vp" nt_vp (by decide)).trans h0_vp
  have h1_un := (hf1 "un" nt_un (by decide)).trans h0_un
  have h1_vn := (hf1 "vn" nt_vn (by decide)).trans h0_vn
  -- step 2: kbr
  obtain ⟨e2, hs2, h2_kbr, hf2⟩ := semScalar_setExpr_run (y := "kbr")
    (lower_cr ones (envReadU64_of_bound h1_t) (envReadU64_of_bound h1_un) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h1_t, envReader_of_bound h1_un] at h2_kbr
  have h2_rp := (hf2 "rp" nt_rp (by decide)).trans h1_rp
  have h2_t := (hf2 "t" nt_t (by decide)).trans h1_t
  have h2_jd := (hf2 "jd" nt_jd (by decide)).trans h1_jd
  have h2_up := (hf2 "up" nt_up (by decide)).trans h1_up
  have h2_vp := (hf2 "vp" nt_vp (by decide)).trans h1_vp
  have h2_un := (hf2 "un" nt_un (by decide)).trans h1_un
  have h2_vn := (hf2 "vn" nt_vn (by decide)).trans h1_vn
  have h2_kbq := (hf2 "kbq" nt_kbq (by decide)).trans h1_kbq
  -- step 3: kb = bSltu tv un
  obtain ⟨e3, hs3, h3_kb, hf3⟩ := semScalar_setExpr_run (y := "kb")
    (lower_orshr 63 (envReadU64_of_bound h2_kbq) (envReadU64_of_bound h2_kbr) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h2_kbq, envReader_of_bound h2_kbr] at h3_kb
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h3_kb
  have h3_rp := (hf3 "rp" nt_rp (by decide)).trans h2_rp
  have h3_t := (hf3 "t" nt_t (by decide)).trans h2_t
  have h3_jd := (hf3 "jd" nt_jd (by decide)).trans h2_jd
  have h3_up := (hf3 "up" nt_up (by decide)).trans h2_up
  have h3_vp := (hf3 "vp" nt_vp (by decide)).trans h2_vp
  have h3_un := (hf3 "un" nt_un (by decide)).trans h2_un
  have h3_vn := (hf3 "vn" nt_vn (by decide)).trans h2_vn
  -- step 4: msk = 0 - bSltu tv un
  obtain ⟨e4, hs4, h4_msk, hf4⟩ := semScalar_setExpr_run (y := "msk")
    (lower_sub0_var (envReadU64_of_bound h3_kb) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h3_kb] at h4_msk
  have h4_rp := (hf4 "rp" nt_rp (by decide)).trans h3_rp
  have h4_t := (hf4 "t" nt_t (by decide)).trans h3_t
  have h4_jd := (hf4 "jd" nt_jd (by decide)).trans h3_jd
  have h4_up := (hf4 "up" nt_up (by decide)).trans h3_up
  have h4_vp := (hf4 "vp" nt_vp (by decide)).trans h3_vp
  have h4_un := (hf4 "un" nt_un (by decide)).trans h3_un
  have h4_vn := (hf4 "vn" nt_vn (by decide)).trans h3_vn
  -- step 5: tm = tv & msk
  obtain ⟨e5, hs5, h5_tm, hf5⟩ := semScalar_setExpr_run (y := "tm")
    (lower_and_vv (envReadU64_of_bound h4_t) (envReadU64_of_bound h4_msk))
  simp only [SExpr.evalBV, envReader_of_bound h4_t, envReader_of_bound h4_msk] at h5_tm
  have h5_rp := (hf5 "rp" nt_rp (by decide)).trans h4_rp
  have h5_t := (hf5 "t" nt_t (by decide)).trans h4_t
  have h5_jd := (hf5 "jd" nt_jd (by decide)).trans h4_jd
  have h5_up := (hf5 "up" nt_up (by decide)).trans h4_up
  have h5_vp := (hf5 "vp" nt_vp (by decide)).trans h4_vp
  have h5_un := (hf5 "un" nt_un (by decide)).trans h4_un
  have h5_msk := (hf5 "msk" nt_msk (by decide)).trans h4_msk
  have h5_vn := (hf5 "vn" nt_vn (by decide)).trans h4_vn
  -- step 6: a0 = up[tm]
  obtain ⟨e6, hs6, h6_a0, hf6⟩ :=
    semScalar_arrLoad (dstN := "a0") (tw := .TBytes (8 * NU)) (idxN := "tm") h5_up h5_tm
  have h6_rp := (hf6 "rp" (by decide)).trans h5_rp
  have h6_t := (hf6 "t" (by decide)).trans h5_t
  have h6_jd := (hf6 "jd" (by decide)).trans h5_jd
  have h6_vp := (hf6 "vp" (by decide)).trans h5_vp
  have h6_un := (hf6 "un" (by decide)).trans h5_un
  have h6_msk := (hf6 "msk" (by decide)).trans h5_msk
  have h6_vn := (hf6 "vn" (by decide)).trans h5_vn
  -- step 7: a = a0 & msk = bcLimb
  obtain ⟨e7, hs7, h7_a, hf7⟩ := semScalar_setExpr_run (y := "a")
    (lower_and_vv (envReadU64_of_bound h6_a0) (envReadU64_of_bound h6_msk))
  simp only [SExpr.evalBV, envReader_of_bound h6_a0, envReader_of_bound h6_msk] at h7_a
  rw [ha_bcSel] at h7_a
  have h7_rp := (hf7 "rp" nt_rp (by decide)).trans h6_rp
  have h7_t := (hf7 "t" nt_t (by decide)).trans h6_t
  have h7_jd := (hf7 "jd" nt_jd (by decide)).trans h6_jd
  have h7_vp := (hf7 "vp" nt_vp (by decide)).trans h6_vp
  have h7_un := (hf7 "un" nt_un (by decide)).trans h6_un
  have h7_vn := (hf7 "vn" nt_vn (by decide)).trans h6_vn
  -- step 8: vv = vp[jd]
  obtain ⟨e8, hs8, h8_vv, hf8⟩ :=
    semScalar_arrLoad (dstN := "vv") (tw := .TBytes (8 * NV)) (idxN := "jd") h7_vp h7_jd
  rw [hjN] at h8_vv
  have h8_rp := (hf8 "rp" (by decide)).trans h7_rp
  have h8_t := (hf8 "t" (by decide)).trans h7_t
  have h8_jd := (hf8 "jd" (by decide)).trans h7_jd
  have h8_un := (hf8 "un" (by decide)).trans h7_un
  have h8_vn := (hf8 "vn" (by decide)).trans h7_vn
  have h8_a := (hf8 "a" (by decide)).trans h7_a
  -- step 9: lo = a * vv
  obtain ⟨e9, hs9, h9_lo, hf9⟩ := semScalar_setExpr_run (y := "lo")
    (lower_mul_vv (envReadU64_of_bound h8_a) (envReadU64_of_bound h8_vv))
  simp only [SExpr.evalBV, envReader_of_bound h8_a, envReader_of_bound h8_vv] at h9_lo
  have h9_rp := (hf9 "rp" nt_rp (by decide)).trans h8_rp
  have h9_t := (hf9 "t" nt_t (by decide)).trans h8_t
  have h9_jd := (hf9 "jd" nt_jd (by decide)).trans h8_jd
  have h9_un := (hf9 "un" nt_un (by decide)).trans h8_un
  have h9_vn := (hf9 "vn" nt_vn (by decide)).trans h8_vn
  have h9_a := (hf9 "a" nt_a (by decide)).trans h8_a
  have h9_vv := (hf9 "vv" nt_vv (by decide)).trans h8_vv
  -- step 10: hi = mulhi(a, vv)
  obtain ⟨e10, hs10, h10_hi, hf10⟩ := semScalar_setExpr_run (y := "hi")
    (lower_hiu_vv (envReadU64_of_bound h9_a) (envReadU64_of_bound h9_vv))
  simp only [SExpr.evalBV, envReader_of_bound h9_a, envReader_of_bound h9_vv, hiU_eq] at h10_hi
  have h10_rp := (hf10 "rp" nt_rp (by decide)).trans h9_rp
  have h10_t := (hf10 "t" nt_t (by decide)).trans h9_t
  have h10_jd := (hf10 "jd" nt_jd (by decide)).trans h9_jd
  have h10_un := (hf10 "un" nt_un (by decide)).trans h9_un
  have h10_vn := (hf10 "vn" nt_vn (by decide)).trans h9_vn
  have h10_lo := (hf10 "lo" nt_lo (by decide)).trans h9_lo
  -- step 11: nc = un + vn
  obtain ⟨e11, hs11, h11_nc, hf11⟩ := semScalar_setExpr_run (y := "nc")
    (lower_add_vv (envReadU64_of_bound h10_un) (envReadU64_of_bound h10_vn))
  simp only [SExpr.evalBV, envReader_of_bound h10_un, envReader_of_bound h10_vn] at h11_nc
  have h11_rp := (hf11 "rp" nt_rp (by decide)).trans h10_rp
  have h11_t := (hf11 "t" nt_t (by decide)).trans h10_t
  have h11_jd := (hf11 "jd" nt_jd (by decide)).trans h10_jd
  have h11_hi := (hf11 "hi" nt_hi (by decide)).trans h10_hi
  have h11_lo := (hf11 "lo" nt_lo (by decide)).trans h10_lo
  -- step 12: cy = rp[nc]
  obtain ⟨e12, hs12, h12_cy, hf12⟩ :=
    semScalar_arrLoad (dstN := "cy") (tw := .TBytes (8 * NR)) (idxN := "nc") h11_rp h11_nc
  rw [hncN] at h12_cy
  have h12_rp := (hf12 "rp" (by decide)).trans h11_rp
  have h12_t := (hf12 "t" (by decide)).trans h11_t
  have h12_jd := (hf12 "jd" (by decide)).trans h11_jd
  have h12_hi := (hf12 "hi" (by decide)).trans h11_hi
  have h12_lo := (hf12 "lo" (by decide)).trans h11_lo
  have h12_nc := (hf12 "nc" (by decide)).trans h11_nc
  -- step 13: s1 = lo + cy
  obtain ⟨e13, hs13, h13_s1, hf13⟩ := semScalar_setExpr_run (y := "s1")
    (lower_add_vv (envReadU64_of_bound h12_lo) (envReadU64_of_bound h12_cy))
  simp only [SExpr.evalBV, envReader_of_bound h12_lo, envReader_of_bound h12_cy] at h13_s1
  have h13_rp := (hf13 "rp" nt_rp (by decide)).trans h12_rp
  have h13_t := (hf13 "t" nt_t (by decide)).trans h12_t
  have h13_jd := (hf13 "jd" nt_jd (by decide)).trans h12_jd
  have h13_hi := (hf13 "hi" nt_hi (by decide)).trans h12_hi
  have h13_lo := (hf13 "lo" nt_lo (by decide)).trans h12_lo
  have h13_nc := (hf13 "nc" nt_nc (by decide)).trans h12_nc
  -- step 14: k1q
  obtain ⟨e14, hs14, h14_k1q, hf14⟩ := semScalar_setExpr_run (y := "k1q")
    (lower_cq ones (envReadU64_of_bound h13_s1) (envReadU64_of_bound h13_lo) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h13_s1, envReader_of_bound h13_lo] at h14_k1q
  have h14_rp := (hf14 "rp" nt_rp (by decide)).trans h13_rp
  have h14_t := (hf14 "t" nt_t (by decide)).trans h13_t
  have h14_jd := (hf14 "jd" nt_jd (by decide)).trans h13_jd
  have h14_hi := (hf14 "hi" nt_hi (by decide)).trans h13_hi
  have h14_lo := (hf14 "lo" nt_lo (by decide)).trans h13_lo
  have h14_nc := (hf14 "nc" nt_nc (by decide)).trans h13_nc
  have h14_s1 := (hf14 "s1" nt_s1 (by decide)).trans h13_s1
  -- step 15: k1r
  obtain ⟨e15, hs15, h15_k1r, hf15⟩ := semScalar_setExpr_run (y := "k1r")
    (lower_cr ones (envReadU64_of_bound h14_s1) (envReadU64_of_bound h14_lo) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h14_s1, envReader_of_bound h14_lo] at h15_k1r
  have h15_rp := (hf15 "rp" nt_rp (by decide)).trans h14_rp
  have h15_t := (hf15 "t" nt_t (by decide)).trans h14_t
  have h15_jd := (hf15 "jd" nt_jd (by decide)).trans h14_jd
  have h15_hi := (hf15 "hi" nt_hi (by decide)).trans h14_hi
  have h15_nc := (hf15 "nc" nt_nc (by decide)).trans h14_nc
  have h15_s1 := (hf15 "s1" nt_s1 (by decide)).trans h14_s1
  have h15_k1q := (hf15 "k1q" nt_k1q (by decide)).trans h14_k1q
  -- step 16: k1 = bSltu s1 lo
  obtain ⟨e16, hs16, h16_k1, hf16⟩ := semScalar_setExpr_run (y := "k1")
    (lower_orshr 63 (envReadU64_of_bound h15_k1q) (envReadU64_of_bound h15_k1r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h15_k1q, envReader_of_bound h15_k1r] at h16_k1
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h16_k1
  have h16_rp := (hf16 "rp" nt_rp (by decide)).trans h15_rp
  have h16_t := (hf16 "t" nt_t (by decide)).trans h15_t
  have h16_jd := (hf16 "jd" nt_jd (by decide)).trans h15_jd
  have h16_hi := (hf16 "hi" nt_hi (by decide)).trans h15_hi
  have h16_nc := (hf16 "nc" nt_nc (by decide)).trans h15_nc
  have h16_s1 := (hf16 "s1" nt_s1 (by decide)).trans h15_s1
  -- step 17: pi = jd + t
  obtain ⟨e17, hs17, h17_pi, hf17⟩ := semScalar_setExpr_run (y := "pi")
    (lower_add_vv (envReadU64_of_bound h16_jd) (envReadU64_of_bound h16_t))
  simp only [SExpr.evalBV, envReader_of_bound h16_jd, envReader_of_bound h16_t] at h17_pi
  have h17_rp := (hf17 "rp" nt_rp (by decide)).trans h16_rp
  have h17_hi := (hf17 "hi" nt_hi (by decide)).trans h16_hi
  have h17_nc := (hf17 "nc" nt_nc (by decide)).trans h16_nc
  have h17_s1 := (hf17 "s1" nt_s1 (by decide)).trans h16_s1
  have h17_k1 := (hf17 "k1" nt_k1 (by decide)).trans h16_k1
  -- step 18: rr = rp[pi]
  obtain ⟨e18, hs18, h18_rr, hf18⟩ :=
    semScalar_arrLoad (dstN := "rr") (tw := .TBytes (8 * NR)) (idxN := "pi") h17_rp h17_pi
  rw [hpiN] at h18_rr
  have h18_rp := (hf18 "rp" (by decide)).trans h17_rp
  have h18_hi := (hf18 "hi" (by decide)).trans h17_hi
  have h18_nc := (hf18 "nc" (by decide)).trans h17_nc
  have h18_s1 := (hf18 "s1" (by decide)).trans h17_s1
  have h18_k1 := (hf18 "k1" (by decide)).trans h17_k1
  have h18_pi := (hf18 "pi" (by decide)).trans h17_pi
  -- step 19: s2 = s1 + rr
  obtain ⟨e19, hs19, h19_s2, hf19⟩ := semScalar_setExpr_run (y := "s2")
    (lower_add_vv (envReadU64_of_bound h18_s1) (envReadU64_of_bound h18_rr))
  simp only [SExpr.evalBV, envReader_of_bound h18_s1, envReader_of_bound h18_rr] at h19_s2
  have h19_rp := (hf19 "rp" nt_rp (by decide)).trans h18_rp
  have h19_hi := (hf19 "hi" nt_hi (by decide)).trans h18_hi
  have h19_nc := (hf19 "nc" nt_nc (by decide)).trans h18_nc
  have h19_s1 := (hf19 "s1" nt_s1 (by decide)).trans h18_s1
  have h19_k1 := (hf19 "k1" nt_k1 (by decide)).trans h18_k1
  have h19_pi := (hf19 "pi" nt_pi (by decide)).trans h18_pi
  -- step 20: k2q
  obtain ⟨e20, hs20, h20_k2q, hf20⟩ := semScalar_setExpr_run (y := "k2q")
    (lower_cq ones (envReadU64_of_bound h19_s2) (envReadU64_of_bound h19_s1) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h19_s2, envReader_of_bound h19_s1] at h20_k2q
  have h20_rp := (hf20 "rp" nt_rp (by decide)).trans h19_rp
  have h20_hi := (hf20 "hi" nt_hi (by decide)).trans h19_hi
  have h20_nc := (hf20 "nc" nt_nc (by decide)).trans h19_nc
  have h20_s1 := (hf20 "s1" nt_s1 (by decide)).trans h19_s1
  have h20_k1 := (hf20 "k1" nt_k1 (by decide)).trans h19_k1
  have h20_pi := (hf20 "pi" nt_pi (by decide)).trans h19_pi
  have h20_s2 := (hf20 "s2" nt_s2 (by decide)).trans h19_s2
  -- step 21: k2r
  obtain ⟨e21, hs21, h21_k2r, hf21⟩ := semScalar_setExpr_run (y := "k2r")
    (lower_cr ones (envReadU64_of_bound h20_s2) (envReadU64_of_bound h20_s1) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h20_s2, envReader_of_bound h20_s1] at h21_k2r
  have h21_rp := (hf21 "rp" nt_rp (by decide)).trans h20_rp
  have h21_hi := (hf21 "hi" nt_hi (by decide)).trans h20_hi
  have h21_nc := (hf21 "nc" nt_nc (by decide)).trans h20_nc
  have h21_s2 := (hf21 "s2" nt_s2 (by decide)).trans h20_s2
  have h21_k1 := (hf21 "k1" nt_k1 (by decide)).trans h20_k1
  have h21_pi := (hf21 "pi" nt_pi (by decide)).trans h20_pi
  have h21_k2q := (hf21 "k2q" nt_k2q (by decide)).trans h20_k2q
  -- step 22: k2 = bSltu s2 s1
  obtain ⟨e22, hs22, h22_k2, hf22⟩ := semScalar_setExpr_run (y := "k2")
    (lower_orshr 63 (envReadU64_of_bound h21_k2q) (envReadU64_of_bound h21_k2r) (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h21_k2q, envReader_of_bound h21_k2r] at h22_k2
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h22_k2
  have h22_rp := (hf22 "rp" nt_rp (by decide)).trans h21_rp
  have h22_hi := (hf22 "hi" nt_hi (by decide)).trans h21_hi
  have h22_nc := (hf22 "nc" nt_nc (by decide)).trans h21_nc
  have h22_s2 := (hf22 "s2" nt_s2 (by decide)).trans h21_s2
  have h22_k1 := (hf22 "k1" nt_k1 (by decide)).trans h21_k1
  have h22_pi := (hf22 "pi" nt_pi (by decide)).trans h21_pi
  -- step 23: hc = (hi + k1) + k2
  obtain ⟨e23, hs23, h23_hc, hf23⟩ := semScalar_setExpr_run (y := "hc")
    (lower_add_add (envReadU64_of_bound h22_hi) (envReadU64_of_bound h22_k1)
      (envReadU64_of_bound h22_k2) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h22_hi, envReader_of_bound h22_k1,
    envReader_of_bound h22_k2] at h23_hc
  have h23_rp := (hf23 "rp" nt_rp (by decide)).trans h22_rp
  have h23_nc := (hf23 "nc" nt_nc (by decide)).trans h22_nc
  have h23_s2 := (hf23 "s2" nt_s2 (by decide)).trans h22_s2
  have h23_pi := (hf23 "pi" nt_pi (by decide)).trans h22_pi
  -- step 24: rp[pi] := s2
  obtain ⟨e24, hs24, h24_rp, hf24⟩ :=
    semScalar_arrStore (fw := 8 * NR) h23_rp h23_pi h23_s2
  rw [hpiN] at h24_rp
  have h24_nc := (hf24 "nc" (by decide)).trans h23_nc
  have h24_hc := (hf24 "hc" (by decide)).trans h23_hc
  -- step 25: rp[nc] := hc
  obtain ⟨e25, hs25, h25_rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h24_rp h24_nc h24_hc
  rw [hncN] at h25_rp
  refine ⟨e25, ?_, ?_⟩
  · rw [rowBody_eq]
    simp only [rowBodyList, notE, orE, sv, upLoc, vpLoc, rpLoc]
    rw [seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8, seqAll_step hs9,
      seqAll_step hs10, seqAll_step hs11, seqAll_step hs12, seqAll_step hs13, seqAll_step hs14,
      seqAll_step hs15, seqAll_step hs16, seqAll_step hs17, seqAll_step hs18, seqAll_step hs19,
      seqAll_step hs20, seqAll_step hs21, seqAll_step hs22, seqAll_step hs23, seqAll_step hs24]
    exact hs25
  · rw [h25_rp]
    simp only [bcStep, mulAddLimb]
    rfl

/-- **The inner-count body computes `un + 1`.** -/
theorem cntBody_run (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un vn : BitVec 64) (jv : BitVec 64) :
    ∃ env',
      semScalar cntBodyLowCT
          (((((emptyEnv.upd "vn" (t := .sword 64) vn).upd "un" (t := .sword 64) un).upd
            "vp" (t := .memref NV) vp).upd "up" (t := .memref NU) up).upd
            "jd" (t := .sword 64) jv) = some env'
        ∧ env' "cnt" = some ⟨.sword 64, un + BitVec.ofNat 64 1⟩ := by
  have hun : (((((emptyEnv.upd "vn" (t := .sword 64) vn).upd "un" (t := .sword 64) un).upd
        "vp" (t := .memref NV) vp).upd "up" (t := .memref NU) up).upd
        "jd" (t := .sword 64) jv) "un" = some ⟨.sword 64, un⟩ := by
    rw [upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
    exact upd_self _ _ _
  obtain ⟨env', hs, hval, -⟩ := semScalar_setExpr_run (y := "cnt")
    (lower_add_lit 1 (envReadU64_of_bound hun) (by decide))
  refine ⟨env', hs, ?_⟩
  rw [hval]
  simp only [SExpr.evalBV, envReader_of_bound hun]

/-! ## 7. The machine-level fold and value theorems -/

/-- The nested double fold unfolds to `bcFold`. -/
theorem bcFold_eq (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un nc n : Nat) (acc : Fin NR → BitVec 64) :
    (List.range n).foldl
        (fun a jd => (List.range (un + 1)).foldl (bcStep up vp un nc jd) a) acc
      = bcFold up vp un nc n acc := rfl

/-- Accessors for the outer argument registers. -/
abbrev upVar : Ctxt.Var Gouter AU := .there (.there (.there .here))
abbrev vpVar : Ctxt.Var Gouter AV := .there (.there .here)
abbrev unVar : Ctxt.Var Gouter r64 := .there .here

/-- **The runtime-trip `mpn_mul_basecase` program denotes the schoolbook fold.**
    The compiled nest's denotation at any valuation is `bcFold` of the argument
    registers, with no front-compilation hypothesis remaining. -/
theorem bcRtProg_fold (V : Ctxt.Valuation Gouter)
    (hscope : (unVar.lookup V).toNat + (bcOuterCount.lookup V).toNat < NR) :
    bcProgOpt.map (fun c => ComL.denote c V)
      = some (bcFold (upVar.lookup V) (vpVar.lookup V) (unVar.lookup V).toNat
          ((unVar.lookup V).toNat + (bcOuterCount.lookup V).toNat)
          (bcOuterCount.lookup V).toNat (bcInit.lookup V)) := by
  rw [bcProg_denote bcCntUpdate_eq bcRowUpdate_eq V]
  refine congrArg some ?_
  set up := upVar.lookup V with hupdef
  set vp := vpVar.lookup V with hvpdef
  set un : BitVec 64 := unVar.lookup V with hundef
  set vn := bcOuterCount.lookup V with hvndef
  set acc := bcInit.lookup V with haccdef
  have hNR : NR < 2 ^ 64 := by decide
  have hun17 : un.toNat < NR := by omega
  have hvn17 : vn.toNat < NR := by omega
  rw [← bcFold_eq up vp un.toNat (un.toNat + vn.toNat) vn.toNat acc]
  refine nestedDenote_foldl (accCTy := .memref NR) (invCTys := Ginv)
    vmBody "rp" rowBodyLowCT rowBody_covered
    (.cons up (.cons vp (.cons un (.cons vn .nil))))
    bcCntUpdate (fun _ => un.toNat + 1)
    (fun jd => bcStep up vp un.toNat (un.toNat + vn.toNat) jd)
    vn.toNat ?_ ?_ bcRowUpdate_eq acc
  · -- hcnt: the inner-count body recomputes un + 1
    intro jd hjd
    have hun1 : un.toNat + 1 < 2 ^ 64 := by omega
    obtain ⟨env', hrun, hcval⟩ := cntBody_run up vp un vn (BitVec.ofNat 64 jd)
    have hcov : IsCoveredSCtl cntBodyLowCT := by
      refine .ofStraight (.rScalarSetExpr _ _ ?_)
      simp only [srcClean, sv]
      repeat' first
        | apply And.intro
        | exact notTmp_of_short _ (by decide)
        | decide
    have key : bcCntUpdate.denote
        (.cons (BitVec.ofNat 64 jd)
          (ctMapValD (.cons up (.cons vp (.cons un (.cons vn .nil))))))
        = un + BitVec.ofNat 64 1 :=
      CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyDenote.frontLoopBodyJ_denote
        (accCTy := .sword 64) vmCount "cnt" cntBodyLowCT hcov
        (.cons (BitVec.ofNat 64 jd) (.cons up (.cons vp (.cons un (.cons vn .nil)))))
        _ env' (un + BitVec.ofNat 64 1)
        (consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
          (consistentS_bind consistentS_empty "vn" (t := .sword 64) vn)
          "un" (t := .sword 64) un) "vp" (t := .memref NV) vp) "up" (t := .memref NU) up)
          "jd" (t := .sword 64) (BitVec.ofNat 64 jd))
        hrun hcval bcCntUpdate_eq
    unfold JLoopBodyN.innerTripAtC
    show (bcCntUpdate.denote (.cons (BitVec.ofNat 64 jd)
        (ctMapValD (.cons up (.cons vp (.cons un (.cons vn .nil))))))).toNat = un.toNat + 1
    rw [key, bv_add_toNat un (BitVec.ofNat 64 1) (by rw [ofNat_toNat (by decide)]; omega),
      ofNat_toNat (by decide)]
  · -- hstep: each trip's source run leaves bcStep
    intro jd hjd t acc' ht
    have ht' : t < un.toNat + 1 := ht
    have hjd' : jd < vn.toNat := hjd
    have httwo : t < 2 ^ 64 := by omega
    have hjtwo : jd < 2 ^ 64 := by omega
    have hpi : jd + t < 2 ^ 64 := by omega
    have hnc : un.toNat + vn.toNat < 2 ^ 64 := by omega
    obtain ⟨env', hrun, hrp⟩ := bcRowBody_run up vp un vn acc' jd t httwo hjtwo hpi hnc
    exact ⟨bcRowEnv acc' (BitVec.ofNat 64 t) (BitVec.ofNat 64 jd) up vp un vn, env',
      consistentS_bcRowEnv acc' (BitVec.ofNat 64 t) (BitVec.ofNat 64 jd) up vp un vn,
      hrun, hrp⟩

/-- **The compiled `mpn_mul_basecase` computes the product.** For runtime limb
    counts within the model's output array and a zeroed accumulator, the compiled
    program's output cells `0, …, un+vn-1` recombine via `bignumVal` to
    `up[0..un) * vp[0..vn)`. -/
theorem bcRtProg_val (V : Ctxt.Valuation Gouter)
    (hscope : (unVar.lookup V).toNat + (bcOuterCount.lookup V).toNat < NR)
    (hz : ∀ i, i < NR → memGetDyn (bcInit.lookup V) i = 0) :
    ∃ out : Fin NR → BitVec 64,
      bcProgOpt.map (fun c => ComL.denote c V) = some out ∧
        bignumVal (MpnMul1FrontEmit.cells out
            ((unVar.lookup V).toNat + (bcOuterCount.lookup V).toNat))
          = bignumVal (MpnMul1FrontEmit.cells (upVar.lookup V) (unVar.lookup V).toNat)
              * bignumVal (MpnMul1FrontEmit.cells (vpVar.lookup V)
                  (bcOuterCount.lookup V).toNat) :=
  ⟨_, bcRtProg_fold V hscope,
    bcFold_val_zero (upVar.lookup V) (vpVar.lookup V) (unVar.lookup V).toNat
      (bcOuterCount.lookup V).toNat (bcInit.lookup V) hscope hz⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote
