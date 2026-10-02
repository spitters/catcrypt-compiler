/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf

/-!
# The `mpn_mul_1` loop body against its source semantics

`MpnMul1FrontEmit.mul1RtProg_denote` states the emitted runtime-trip loop's
denotation as the `JLoopBodyN` fold of `update`, under the hypothesis
`frontLoopBodyJ … = some update`. This module supplies that `update`, runs the
source `LowCT` limb body symbolically through `semScalar` from the canonical
per-trip entry state, and identifies each trip with the word-model step
`mul1FoldStep` — so the model-level value theorem `mul1Fold_val_zero` reads on
the compiled program's denotation.

The per-trip run is the finite per-command check: two `RArrLoad`s, eight
`RScalarSetExpr`s, two `RArrStore`s, each stepped by the waist lemmas of
`Secp256k1PointOpFrameRoundTrip`. The two word identities it needs are
`hiU_eq` (the `SMulHiU` evaluator is `mulHiW`) and `ltu_chain` (the emitted
xor/and carry idiom is `bSltu`).

## Main results

* `limbBody_coveredS` / `limbBody_covered` — the limb body is covered
  straight-line `LowCT`.
* `mul1Update` / `mul1Update_eq` — the front-compiled limb body and the
  equation discharging `mul1RtProg_denote`'s hypothesis.
* `limbBody_run` — the per-trip `semScalar` run: from the canonical entry
  state at trip `t`, the body leaves `mul1FoldStep up b acc t` in `rp`.
* `mul1RtProg_fold` — the runtime-trip program's denotation is the
  `mul1Fold` word-model fold, with no remaining hypothesis.
* `mul1RtProg_val` — the machine-level value theorem: the compiled program's
  output cells recombine via `bignumVal` to `up[0..n) * v`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

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
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## Precomputed name-freshness

Each source variable's not-a-temporary fact is proved once — the `by decide` on
the below-`4` name length is paid a single time per name — and referenced at the
freshness sites below, instead of re-deciding the string length at each site. -/

theorem nt_c : ¬ isTmpName "c" := notTmp_of_short _ (by decide)
theorem nt_cq : ¬ isTmpName "cq" := notTmp_of_short _ (by decide)
theorem nt_cr : ¬ isTmpName "cr" := notTmp_of_short _ (by decide)
theorem nt_cy : ¬ isTmpName "cy" := notTmp_of_short _ (by decide)
theorem nt_cyo : ¬ isTmpName "cyo" := notTmp_of_short _ (by decide)
theorem nt_hi : ¬ isTmpName "hi" := notTmp_of_short _ (by decide)
theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_lo : ¬ isTmpName "lo" := notTmp_of_short _ (by decide)
theorem nt_rp : ¬ isTmpName "rp" := notTmp_of_short _ (by decide)
theorem nt_s : ¬ isTmpName "s" := notTmp_of_short _ (by decide)
theorem nt_t : ¬ isTmpName "t" := notTmp_of_short _ (by decide)
theorem nt_v : ¬ isTmpName "v" := notTmp_of_short _ (by decide)

/-! ## 1. Sequencing and name plumbing -/

/-- A short source name misses the whole reserved `__sx` index range. -/
theorem ne_tmp_of_short {x : String} (h : x.length < 4) (k : Nat) : x ≠ tmpName k :=
  fun hh => notTmp_of_short x h ⟨k, hh⟩

/-- Peel the head of an `MpnMul1FrontEmit.seqAll` chain. -/
theorem semScalar_seqAll_cons (c : LowCT) (l : List LowCT) (env : SEnvScalar) :
    semScalar (seqAll (c :: l)) env
      = (semScalar c env).bind (fun e => semScalar (seqAll l) e) := by
  cases l with
  | nil =>
      show semScalar c env = _
      cases semScalar c env <;> rfl
  | cons d ds => rfl

/-- Peel the head of a `seqAll` whose head command steps. -/
theorem seqAll_step {c : LowCT} {l : List LowCT} {env e : SEnvScalar}
    (h : semScalar c env = some e) :
    semScalar (seqAll (c :: l)) env = semScalar (seqAll l) e := by
  rw [semScalar_seqAll_cons, h]
  rfl

/-! ## 2. Progress of the five `SExpr` shapes the limb body uses -/

theorem lower_mul_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SMul (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

theorem lower_hiu_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SMulHiU (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

theorem lower_add_vv {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SAdd (.SVar x) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode]
  rfl

theorem lower_add_lit {env : SEnvScalar} {x : String} {wx : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SAdd (.SVar x) (.SLit L))).isSome := by
  simp only [semLowerSExpr, hx, binNode, envReadU64_upd_ne (ne_tmp_of_short hxl 0),
    envReadU64_upd_self]
  rfl

theorem lower_cq {env : SEnvScalar} {x y : String} {wx wy : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hxl : x.length < 4) (hyl : y.length < 4) :
    (semLowerSExpr env 0 (.SAnd (.SXor (.SVar x) (.SLit L)) (.SVar y))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), envReadU64_upd_ne (ne_tmp_of_short hyl 0),
    envReadU64_upd_ne (ne_tmp_of_short hyl 1), envReadU64_upd_self]
  rfl

theorem lower_cr {env : SEnvScalar} {x y : String} {wx wy : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hxl : x.length < 4) (hyl : y.length < 4) :
    (semLowerSExpr env 0
      (.SAnd (.SXor (.SXor (.SVar x) (.SVar y)) (.SLit L))
        (.SSub (.SVar x) (.SVar y)))).isSome := by
  simp only [semLowerSExpr, hx, hy, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hxl 0), envReadU64_upd_ne (ne_tmp_of_short hyl 0),
    envReadU64_upd_ne (ne_tmp_of_short hxl 1), envReadU64_upd_ne (ne_tmp_of_short hyl 1),
    envReadU64_upd_ne (ne_tmp_of_short hxl 2), envReadU64_upd_ne (ne_tmp_of_short hyl 2),
    envReadU64_upd_ne (show tmpName 0 ≠ tmpName 1 by decide),
    envReadU64_upd_ne (show tmpName 2 ≠ tmpName 3 by decide),
    envReadU64_upd_self]
  rfl

theorem lower_orshr {env : SEnvScalar} {p q : String} {wp wq : BitVec 64} (L : Nat)
    (hp : envReadU64 env p = some wp) (hq : envReadU64 env q = some wq)
    (hpl : p.length < 4) (hql : q.length < 4) :
    (semLowerSExpr env 0
      (.SShr (.SXor (.SXor (.SVar p) (.SVar q)) (.SAnd (.SVar p) (.SVar q)))
        (.SLit L))).isSome := by
  simp only [semLowerSExpr, hp, hq, binNode,
    envReadU64_upd_ne (ne_tmp_of_short hpl 0), envReadU64_upd_ne (ne_tmp_of_short hql 0),
    envReadU64_upd_ne (show tmpName 0 ≠ tmpName 1 by decide),
    envReadU64_upd_ne (show tmpName 2 ≠ tmpName 3 by decide),
    envReadU64_upd_self]
  rfl

/-! ## 3. The two word identities of the limb step -/

/-- The wrapping-`u64` `SMulHiU` evaluator is the `MULX` high word. -/
theorem hiU_eq (a b : BitVec 64) :
    BitVec.ofNat 64 (CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU a.toNat b.toNat)
      = mulHiW a b := by
  simp [CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU, mulHiW,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt, Nat.shiftRight_eq_div_pow]

/-- The emitted xor/and carry idiom — `notE`/`orE` over the covered `SExpr`
    alphabet — is `bSltu`. -/
theorem ltu_chain (x y : BitVec 64) :
    ((((x ^^^ BitVec.ofNat 64 ones) &&& y)
        ^^^ (((x ^^^ y) ^^^ BitVec.ofNat 64 ones) &&& (x - y)))
      ^^^ (((x ^^^ BitVec.ofNat 64 ones) &&& y)
        &&& (((x ^^^ y) ^^^ BitVec.ofNat 64 ones) &&& (x - y)))) >>> 63
      = bSltu x y := by
  simp only [ones, CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms.bSltu]
  bv_decide

/-! ## 4. The canonical per-trip entry state -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of the limb body at one trip: the output
    array at `rp`, the trip index at `idx`, the scalar multiplier at `v`, the
    multiplicand array at `up`. -/
def mul1Env (up : Fin NU → BitVec 64) (b : BitVec 64) (acc : Fin NR → BitVec 64)
    (iv : BitVec 64) : SEnvScalar :=
  ((((emptyEnv.upd "up" (t := .memref NU) up).upd
      "v" (t := .sword 64) b).upd
      "idx" (t := .sword 64) iv).upd "rp" (t := .memref NR) acc)

/-- The canonical entry state is consistent with `vmBody` and the trip
    valuation. -/
theorem consistentS_mul1Env (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    ConsistentS vmBody
      (.cons acc (.cons iv (.cons b (.cons up .nil)))) (mul1Env up b acc iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    consistentS_empty "up" (t := .memref NU) up) "v" (t := .sword 64) b)
    "idx" (t := .sword 64) iv) "rp" (t := .memref NR) acc

theorem mul1Env_rp (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mul1Env up b acc iv "rp" = some ⟨.memref NR, acc⟩ := upd_self _ _ _

theorem mul1Env_idx (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mul1Env up b acc iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [mul1Env, upd_ne (by decide)]; exact upd_self _ _ _

theorem mul1Env_v (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mul1Env up b acc iv "v" = some ⟨.sword 64, b⟩ := by
  rw [mul1Env, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem mul1Env_up (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (iv : BitVec 64) :
    mul1Env up b acc iv "up" = some ⟨.memref NU, up⟩ := by
  rw [mul1Env, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 5. The per-trip run of the limb body -/

/-- **The limb body computes one `mul1FoldStep`.** From the canonical entry
    state at trip `t`, the source body's `semScalar` run terminates and leaves
    exactly the word-model step's array in `rp`: the product's low word at cell
    `t` and the carry-out at cell `t + 1`. The per-command check of the seam,
    stepped through the twelve commands. -/
theorem limbBody_run (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t + 1 < 2 ^ 64) :
    ∃ env', semScalar limbBodyLowCT (mul1Env up b acc (BitVec.ofNat 64 t)) = some env'
      ∧ env' "rp" = some ⟨.memref NR, mul1FoldStep up b acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by
    simp only [hivdef, BitVec.toNat_ofNat]
    omega
  have hiv1N : (iv + BitVec.ofNat 64 1).toNat = t + 1 := by
    simp only [BitVec.toNat_add, hivN, BitVec.toNat_ofNat]
    omega
  have hbody : limbBodyLowCT = seqAll
    [ .RArrLoad ⟨"cy", .TU64⟩ ⟨"rp", .TBytes (8 * NR)⟩ "idx"
    , .RArrLoad ⟨"t", .TU64⟩ ⟨"up", .TBytes (8 * NU)⟩ "idx"
    , .RScalarSetExpr "lo" (.SMul (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "hi" (.SMulHiU (.SVar "t") (.SVar "v"))
    , .RScalarSetExpr "s" (.SAdd (.SVar "lo") (.SVar "cy"))
    , .RScalarSetExpr "cq" (.SAnd (.SXor (.SVar "s") (.SLit ones)) (.SVar "lo"))
    , .RScalarSetExpr "cr" (.SAnd (.SXor (.SXor (.SVar "s") (.SVar "lo")) (.SLit ones))
        (.SSub (.SVar "s") (.SVar "lo")))
    , .RScalarSetExpr "c" (.SShr (.SXor (.SXor (.SVar "cq") (.SVar "cr"))
        (.SAnd (.SVar "cq") (.SVar "cr"))) (.SLit 63))
    , .RScalarSetExpr "cyo" (.SAdd (.SVar "hi") (.SVar "c"))
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "idx" ⟨"s", .TU64⟩
    , .RScalarSetExpr "idx1" (.SAdd (.SVar "idx") (.SLit 1))
    , .RArrStore ⟨"rp", .TBytes (8 * NR)⟩ "idx1" ⟨"cyo", .TU64⟩ ] := rfl
  -- step 1: cy := rp[idx]
  obtain ⟨e1, hs1, h1cy, hf1⟩ :=
    semScalar_arrLoad (dstN := "cy") (tw := .TBytes (8 * NR)) (idxN := "idx")
      (mul1Env_rp up b acc iv) (mul1Env_idx up b acc iv)
  rw [hivN] at h1cy
  have h1rp := (hf1 "rp" (by decide)).trans (mul1Env_rp up b acc iv)
  have h1up := (hf1 "up" (by decide)).trans (mul1Env_up up b acc iv)
  have h1idx := (hf1 "idx" (by decide)).trans (mul1Env_idx up b acc iv)
  have h1v := (hf1 "v" (by decide)).trans (mul1Env_v up b acc iv)
  -- step 2: t := up[idx]
  obtain ⟨e2, hs2, h2t, hf2⟩ :=
    semScalar_arrLoad (dstN := "t") (tw := .TBytes (8 * NU)) (idxN := "idx") h1up h1idx
  rw [hivN] at h2t
  have h2rp := (hf2 "rp" (by decide)).trans h1rp
  have h2idx := (hf2 "idx" (by decide)).trans h1idx
  have h2v := (hf2 "v" (by decide)).trans h1v
  have h2cy := (hf2 "cy" (by decide)).trans h1cy
  -- step 3: lo := t * v
  obtain ⟨e3, hs3, h3lo, hf3⟩ := semScalar_setExpr_run (y := "lo")
    (lower_mul_vv (envReadU64_of_bound h2t) (envReadU64_of_bound h2v))
  simp only [SExpr.evalBV, envReader_of_bound h2t, envReader_of_bound h2v] at h3lo
  have h3rp := (hf3 "rp" (nt_rp) (by decide)).trans h2rp
  have h3idx := (hf3 "idx" (nt_idx) (by decide)).trans h2idx
  have h3v := (hf3 "v" (nt_v) (by decide)).trans h2v
  have h3cy := (hf3 "cy" (nt_cy) (by decide)).trans h2cy
  have h3t := (hf3 "t" (nt_t) (by decide)).trans h2t
  -- step 4: hi := mulhi(t, v)
  obtain ⟨e4, hs4, h4hi, hf4⟩ := semScalar_setExpr_run (y := "hi")
    (lower_hiu_vv (envReadU64_of_bound h3t) (envReadU64_of_bound h3v))
  simp only [SExpr.evalBV, envReader_of_bound h3t, envReader_of_bound h3v, hiU_eq] at h4hi
  have h4rp := (hf4 "rp" (nt_rp) (by decide)).trans h3rp
  have h4idx := (hf4 "idx" (nt_idx) (by decide)).trans h3idx
  have h4cy := (hf4 "cy" (nt_cy) (by decide)).trans h3cy
  have h4lo := (hf4 "lo" (nt_lo) (by decide)).trans h3lo
  -- step 5: s := lo + cy
  obtain ⟨e5, hs5, h5s, hf5⟩ := semScalar_setExpr_run (y := "s")
    (lower_add_vv (envReadU64_of_bound h4lo) (envReadU64_of_bound h4cy))
  simp only [SExpr.evalBV, envReader_of_bound h4lo, envReader_of_bound h4cy] at h5s
  have h5rp := (hf5 "rp" (nt_rp) (by decide)).trans h4rp
  have h5idx := (hf5 "idx" (nt_idx) (by decide)).trans h4idx
  have h5hi := (hf5 "hi" (nt_hi) (by decide)).trans h4hi
  have h5lo := (hf5 "lo" (nt_lo) (by decide)).trans h4lo
  -- step 6: cq := (~s) & lo
  obtain ⟨e6, hs6, h6cq, hf6⟩ := semScalar_setExpr_run (y := "cq")
    (lower_cq ones (envReadU64_of_bound h5s) (envReadU64_of_bound h5lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h5s, envReader_of_bound h5lo] at h6cq
  have h6rp := (hf6 "rp" (nt_rp) (by decide)).trans h5rp
  have h6idx := (hf6 "idx" (nt_idx) (by decide)).trans h5idx
  have h6hi := (hf6 "hi" (nt_hi) (by decide)).trans h5hi
  have h6s := (hf6 "s" (nt_s) (by decide)).trans h5s
  have h6lo := (hf6 "lo" (nt_lo) (by decide)).trans h5lo
  -- step 7: cr := (~(s ^ lo)) & (s - lo)
  obtain ⟨e7, hs7, h7cr, hf7⟩ := semScalar_setExpr_run (y := "cr")
    (lower_cr ones (envReadU64_of_bound h6s) (envReadU64_of_bound h6lo)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h6s, envReader_of_bound h6lo] at h7cr
  have h7rp := (hf7 "rp" (nt_rp) (by decide)).trans h6rp
  have h7idx := (hf7 "idx" (nt_idx) (by decide)).trans h6idx
  have h7hi := (hf7 "hi" (nt_hi) (by decide)).trans h6hi
  have h7s := (hf7 "s" (nt_s) (by decide)).trans h6s
  have h7cq := (hf7 "cq" (nt_cq) (by decide)).trans h6cq
  -- step 8: c := ((cq | cr) >> 63)
  obtain ⟨e8, hs8, h8c, hf8⟩ := semScalar_setExpr_run (y := "c")
    (lower_orshr 63 (envReadU64_of_bound h7cq) (envReadU64_of_bound h7cr)
      (by decide) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h7cq, envReader_of_bound h7cr] at h8c
  rw [show (BitVec.ofNat 64 63).toNat = 63 from rfl, ltu_chain] at h8c
  have h8rp := (hf8 "rp" (nt_rp) (by decide)).trans h7rp
  have h8idx := (hf8 "idx" (nt_idx) (by decide)).trans h7idx
  have h8hi := (hf8 "hi" (nt_hi) (by decide)).trans h7hi
  have h8s := (hf8 "s" (nt_s) (by decide)).trans h7s
  -- step 9: cyo := hi + c
  obtain ⟨e9, hs9, h9cyo, hf9⟩ := semScalar_setExpr_run (y := "cyo")
    (lower_add_vv (envReadU64_of_bound h8hi) (envReadU64_of_bound h8c))
  simp only [SExpr.evalBV, envReader_of_bound h8hi, envReader_of_bound h8c] at h9cyo
  have h9rp := (hf9 "rp" (nt_rp) (by decide)).trans h8rp
  have h9idx := (hf9 "idx" (nt_idx) (by decide)).trans h8idx
  have h9s := (hf9 "s" (nt_s) (by decide)).trans h8s
  -- step 10: rp[idx] := s
  obtain ⟨e10, hs10, h10rp, hf10⟩ :=
    semScalar_arrStore (fw := 8 * NR) h9rp h9idx h9s
  rw [hivN] at h10rp
  have h10idx := (hf10 "idx" (by decide)).trans h9idx
  have h10cyo := (hf10 "cyo" (by decide)).trans h9cyo
  -- step 11: idx1 := idx + 1
  obtain ⟨e11, hs11, h11idx1, hf11⟩ := semScalar_setExpr_run (y := "idx1")
    (lower_add_lit 1 (envReadU64_of_bound h10idx) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h10idx] at h11idx1
  have h11rp := (hf11 "rp" (nt_rp) (by decide)).trans h10rp
  have h11cyo := (hf11 "cyo" (nt_cyo) (by decide)).trans h10cyo
  -- step 12: rp[idx1] := cyo
  obtain ⟨e12, hs12, h12rp, -⟩ :=
    semScalar_arrStore (fw := 8 * NR) h11rp h11idx1 h11cyo
  rw [hiv1N] at h12rp
  refine ⟨e12, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8,
      seqAll_step hs9, seqAll_step hs10, seqAll_step hs11]
    exact hs12
  · rw [h12rp]
    simp only [mul1FoldStep, mul1Limb]
    rfl

/-! ## 6. Coverage -/

/-- Literal bound for the all-ones mask. -/
theorem hones : ones < 2 ^ 64 := by decide

/-- The limb body is covered straight-line `LowCT`: two dynamic array reads,
    eight `srcClean` scalar assignments, two dynamic array writes. -/
theorem limbBody_coveredS : IsCoveredS limbBodyLowCT :=
  .rSeq (.rArrLoad _ _ _)
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
                      ⟨nt_hi, nt_c⟩)
                    (.rSeq (.rArrStore _ _ _)
                      (.rSeq (.rScalarSetExpr _ _
                          ⟨nt_idx,
                            (by decide : (1 : Nat) < 2 ^ 64)⟩)
                        (.rArrStore _ _ _)))))))))))

/-- The limb body sits in the control-extended covered fragment. -/
theorem limbBody_covered : IsCoveredSCtl limbBodyLowCT := .ofStraight limbBody_coveredS

/-! ## 7. The front-compiled body -/

/-- The front accepts the limb body. -/
theorem mul1FrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" limbBodyLowCT).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_mul_1` limb body. -/
def mul1Update : Com jasminDialect (mapCtx Gbody) (mapTy (CryptoTy.memref NR)) :=
  (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" limbBodyLowCT).get mul1FrontOk

/-- The equation `mul1RtProg_denote` takes as its hypothesis. -/
theorem mul1Update_eq :
    frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" limbBodyLowCT = some mul1Update :=
  (Option.some_get mul1FrontOk).symm

/-- The scalar-multiplier argument (RCX). -/
abbrev vVar : Ctxt.Var Gouter r64 := .here

/-- The multiplicand-array argument (RSI). -/
abbrev upVar : Ctxt.Var Gouter AU := .there (.there .here)

/-! ## 8. The machine-level fold and value theorems -/

/-- **The runtime-trip `mpn_mul_1` program denotes the word-model fold.** The
    compiled program's denotation at any valuation is `mul1Fold` of the
    argument registers — the trip count read from `n`, the multiplicand array
    and scalar threaded as invariants, the output array as the accumulator
    seed. No front-compilation hypothesis remains. -/
theorem mul1RtProg_fold (V : Ctxt.Valuation Gouter) :
    (mul1RtProgOpt ()).map (fun c => ComL.denote c V)
      = some (mul1Fold (upVar.lookup V) (vVar.lookup V)
          (mul1Count.lookup V).toNat (mul1Init.lookup V)) := by
  rw [mul1RtProg_denote (update := mul1Update) mul1Update_eq V]
  congr 1
  have h64 := (mul1Count.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .memref NR)
    (invCTys := [.sword 64, .memref NU]) vmBody "rp" limbBodyLowCT limbBody_covered
    (.cons (vVar.lookup V) (.cons (upVar.lookup V) .nil))
    (fun arr tt => mul1FoldStep (upVar.lookup V) (vVar.lookup V) arr tt)
    (mul1Count.lookup V).toNat
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ :=
        limbBody_run (upVar.lookup V) (vVar.lookup V) arr tt (by omega)
      exact ⟨mul1Env (upVar.lookup V) (vVar.lookup V) arr (BitVec.ofNat 64 tt), env',
        consistentS_mul1Env (upVar.lookup V) (vVar.lookup V) arr (BitVec.ofNat 64 tt),
        hrun, hrp⟩)
    mul1Update_eq (mul1Init.lookup V)

/-- **The compiled `mpn_mul_1` computes the product.** For a trip count within
    the model's output array and a zeroed carry seed, the compiled program's
    output cells `0, …, n` recombine via `bignumVal` to `up[0..n) * v` — the
    model-level `mul1Fold_val_zero`, read on the machine-level denotation
    through the seam. -/
theorem mul1RtProg_val (V : Ctxt.Valuation Gouter)
    (hn : (mul1Count.lookup V).toNat < NR)
    (h0 : memGetDyn (mul1Init.lookup V) 0 = 0) :
    ∃ out : Fin NR → BitVec 64,
      (mul1RtProgOpt ()).map (fun c => ComL.denote c V) = some out ∧
        bignumVal (cells out ((mul1Count.lookup V).toNat + 1))
          = bignumVal (cells (upVar.lookup V) (mul1Count.lookup V).toNat)
              * (vVar.lookup V).toNat :=
  ⟨_, mul1RtProg_fold V,
    mul1Fold_val_zero (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
      (mul1Count.lookup V).toNat hn h0⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
