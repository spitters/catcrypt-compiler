/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# The shipped bitwise limb bodies against their source semantics

`MpnLoopBytesEmit.kernels` maps the linked `mpn_{and,ior,xor}_n_loop_owned` to
`MpnLoopFrontEmit.binLprog`, whose limb body is `binBody op` over the context
`ΓbodyBin = [out, idx, a, b]` at `N = 4` words. `MpnLogicalFrontDenote` identifies the fold of
a different body (`logicBodyLowCT`, `NL = 8`, slots `rp`/`ap`/`bp`) with `logicFold`; this
module does the same for `binBody`: it runs the source body symbolically through `semScalar`
from the canonical per-trip entry state (`binLimbBody_run`) and concludes with
`frontLoopBodyJ_denote_foldl` that `JLoopBodyN.denote` of the front-compiled body is the
`logicFold` of the combiner (`binFold_denote`).

## Main results

* `binLimbBody_run` — one trip of `binBody op` is `logicFoldStep f`.
* `binFold_denote` — `JLoopBodyN.denote ⟨n, u⟩ (a, b) acc = logicFold f a b n acc` for the
  front-compiled `u` of `binBody op`.
* `binAnd_denote`, `binXor_denote`, `binIor_denote` — the three shipped combiners.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinFrontDenote

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (JLoopBodyN)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredS IsCoveredSCtl isTmpName
   envReadU64 envReader semLowerSExpr consistentS_empty)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC
  (consistentS_bind frontLoopBodyJ_denote_foldl)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (upd_ne upd_self envReadU64_of_bound envReader_of_bound semScalar_arrLoad
   semScalar_arrStore semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Ascent (notTmp_of_short)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (sv seqAll)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (seqAll_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
  (logicFoldStep logicFold)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
  (emptyEnv lower_and_vv lower_xor_vv lower_ior_vv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit (binBody vmBin ΓbodyBin)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_out : ¬ isTmpName "out" := notTmp_of_short _ (by decide)
theorem nt_ix : ¬ isTmpName "ix" := notTmp_of_short _ (by decide)
theorem nt_ai : ¬ isTmpName "ai" := notTmp_of_short _ (by decide)
theorem nt_bi : ¬ isTmpName "bi" := notTmp_of_short _ (by decide)
theorem nt_a : ¬ isTmpName "a" := notTmp_of_short _ (by decide)
theorem nt_b : ¬ isTmpName "b" := notTmp_of_short _ (by decide)

/-! ## 1. The canonical per-trip entry state -/

/-- The canonical entry environment of the limb body at one trip: the output array at
    `out`, the trip index at `idx`, the sources at `a` and `b`. -/
def binEnv (a b acc : Fin N → BitVec 64) (iv : BitVec 64) : SEnvScalar :=
  ((((emptyEnv.upd "b" (t := .memref N) b).upd
      "a" (t := .memref N) a).upd
      "idx" (t := .sword 64) iv).upd "out" (t := .memref N) acc)

theorem consistentS_binEnv (a b acc : Fin N → BitVec 64) (iv : BitVec 64) :
    ConsistentS vmBin
      (.cons acc (.cons iv (.cons a (.cons b .nil)))) (binEnv a b acc iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    consistentS_empty "b" (t := .memref N) b) "a" (t := .memref N) a)
    "idx" (t := .sword 64) iv) "out" (t := .memref N) acc

theorem binEnv_out (a b acc : Fin N → BitVec 64) (iv : BitVec 64) :
    binEnv a b acc iv "out" = some ⟨.memref N, acc⟩ := upd_self _ _ _

theorem binEnv_idx (a b acc : Fin N → BitVec 64) (iv : BitVec 64) :
    binEnv a b acc iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [binEnv, upd_ne (by decide)]; exact upd_self _ _ _

theorem binEnv_a (a b acc : Fin N → BitVec 64) (iv : BitVec 64) :
    binEnv a b acc iv "a" = some ⟨.memref N, a⟩ := by
  rw [binEnv, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem binEnv_b (a b acc : Fin N → BitVec 64) (iv : BitVec 64) :
    binEnv a b acc iv "b" = some ⟨.memref N, b⟩ := by
  rw [binEnv, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

/-! ## 2. The parametric per-trip run -/

/-- **One trip of `binBody op` is one `logicFoldStep`.** -/
theorem binLimbBody_run (f : BitVec 64 → BitVec 64 → BitVec 64)
    (op : SExpr → SExpr → SExpr)
    (hlow : ∀ {env : SEnvScalar} {wx wy : BitVec 64},
      envReadU64 env "ai" = some wx → envReadU64 env "bi" = some wy →
      (semLowerSExpr env 0 (op (.SVar "ai") (.SVar "bi"))).isSome)
    (heval : ∀ β : String → BitVec 64,
      SExpr.evalBV β (op (.SVar "ai") (.SVar "bi")) = f (β "ai") (β "bi"))
    (a b acc : Fin N → BitVec 64) (t : Nat) (ht : t < 2 ^ 64) :
    ∃ env', semScalar (binBody op) (binEnv a b acc (BitVec.ofNat 64 t)) = some env'
      ∧ env' "out" = some ⟨.memref N, logicFoldStep f a b acc t⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by simp only [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : binBody op = seqAll
    [ .RScalarSetExpr "ix" (.SVar "idx")
    , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
    , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
    , .RScalarSetExpr "r" (op (.SVar "ai") (.SVar "bi"))
    , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ] := rfl
  -- step 0: ix := idx
  have hlow0 : (semLowerSExpr (binEnv a b acc iv) 0 (.SVar "idx")).isSome := by
    simp only [semLowerSExpr, envReadU64_of_bound (binEnv_idx a b acc iv)]; rfl
  obtain ⟨e0, hs0, h0ix, hf0⟩ := semScalar_setExpr_run (y := "ix") hlow0
  rw [show SExpr.evalBV (envReader (binEnv a b acc iv)) (.SVar "idx") = iv from
    envReader_of_bound (binEnv_idx a b acc iv)] at h0ix
  have h0out := (hf0 "out" nt_out (by decide)).trans (binEnv_out a b acc iv)
  have h0a := (hf0 "a" nt_a (by decide)).trans (binEnv_a a b acc iv)
  have h0b := (hf0 "b" nt_b (by decide)).trans (binEnv_b a b acc iv)
  -- step 1: ai := a[ix]
  obtain ⟨e1, hs1, h1ai, hf1⟩ :=
    semScalar_arrLoad (dstN := "ai") (tw := .TBytes (8 * N)) (idxN := "ix") h0a h0ix
  rw [hivN] at h1ai
  have h1out := (hf1 "out" (by decide)).trans h0out
  have h1b := (hf1 "b" (by decide)).trans h0b
  have h1ix := (hf1 "ix" (by decide)).trans h0ix
  -- step 2: bi := b[ix]
  obtain ⟨e2, hs2, h2bi, hf2⟩ :=
    semScalar_arrLoad (dstN := "bi") (tw := .TBytes (8 * N)) (idxN := "ix") h1b h1ix
  rw [hivN] at h2bi
  have h2out := (hf2 "out" (by decide)).trans h1out
  have h2ix := (hf2 "ix" (by decide)).trans h1ix
  have h2ai := (hf2 "ai" (by decide)).trans h1ai
  -- step 3: r := op ai bi
  obtain ⟨e3, hs3, h3r, hf3⟩ := semScalar_setExpr_run (y := "r")
    (hlow (envReadU64_of_bound h2ai) (envReadU64_of_bound h2bi))
  rw [heval (envReader e2), envReader_of_bound h2ai, envReader_of_bound h2bi] at h3r
  have h3out := (hf3 "out" nt_out (by decide)).trans h2out
  have h3ix := (hf3 "ix" nt_ix (by decide)).trans h2ix
  -- step 4: out[ix] := r
  obtain ⟨e4, hs4, h4out, -⟩ :=
    semScalar_arrStore (fw := 8 * N) h3out h3ix h3r
  rw [hivN] at h4out
  refine ⟨e4, ?_, ?_⟩
  · rw [hbody, seqAll_step hs0, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3]
    exact hs4
  · rw [h4out]; rfl


/-! ## 3. Coverage -/

theorem binAndBody_covered : IsCoveredSCtl (binBody .SAnd) :=
  .ofStraight (.rSeq (.rScalarSetExpr _ _ nt_idx)
    (.rSeq (.rArrLoad _ _ _) (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _ ⟨nt_ai, nt_bi⟩) (.rArrStore _ _ _)))))

theorem binXorBody_covered : IsCoveredSCtl (binBody .SXor) :=
  .ofStraight (.rSeq (.rScalarSetExpr _ _ nt_idx)
    (.rSeq (.rArrLoad _ _ _) (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _ ⟨nt_ai, nt_bi⟩) (.rArrStore _ _ _)))))

theorem binIorBody_covered :
    IsCoveredSCtl (binBody (fun x y => .SXor (.SXor x y) (.SAnd x y))) :=
  .ofStraight (.rSeq (.rScalarSetExpr _ _ nt_idx)
    (.rSeq (.rArrLoad _ _ _) (.rSeq (.rArrLoad _ _ _)
      (.rSeq (.rScalarSetExpr _ _ ⟨⟨nt_ai, nt_bi⟩, ⟨nt_ai, nt_bi⟩⟩) (.rArrStore _ _ _)))))

/-! ## 4. The fold -/

/-- **The front-compiled `binBody op` folds `logicFoldStep f`.** For the front-compiled
    body `u` of `binBody op`, at the sources `a`, `b` and the seed `acc`, the `n`-trip
    `JLoopBodyN.denote` is `logicFold f a b n acc`. -/
theorem binFold_denote (f : BitVec 64 → BitVec 64 → BitVec 64)
    (op : SExpr → SExpr → SExpr)
    (hlow : ∀ {env : SEnvScalar} {wx wy : BitVec 64},
      envReadU64 env "ai" = some wx → envReadU64 env "bi" = some wy →
      (semLowerSExpr env 0 (op (.SVar "ai") (.SVar "bi"))).isSome)
    (heval : ∀ β : String → BitVec 64,
      SExpr.evalBV β (op (.SVar "ai") (.SVar "bi")) = f (β "ai") (β "bi"))
    (hcov : IsCoveredSCtl (binBody op))
    {u : Com jasminDialect (mapCtx ΓbodyBin) (mapTy (CryptoTy.memref N))}
    (hupd : frontLoopBodyJ (accCTy := .memref N) vmBin "out" (binBody op) = some u)
    (a b acc : Fin N → BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    JLoopBodyN.denote (accTy := mapTy (CryptoTy.memref N))
        (invTys := mapCtx [CryptoTy.memref N, CryptoTy.memref N]) ⟨n, u⟩
        (.cons a (.cons b .nil)) acc
      = logicFold f a b n acc :=
  frontLoopBodyJ_denote_foldl (accCTy := .memref N)
    (invCTys := [.memref N, .memref N]) vmBin "out" (binBody op) hcov
    (.cons a (.cons b .nil)) (fun arr tt => logicFoldStep f a b arr tt) n
    (fun tt arr htt => by
      obtain ⟨env', hrun, hout⟩ := binLimbBody_run f op hlow heval a b arr tt (by omega)
      exact ⟨binEnv a b arr (BitVec.ofNat 64 tt), env',
        consistentS_binEnv a b arr (BitVec.ofNat 64 tt), hrun, hout⟩)
    hupd acc

/-- The conjunction body. -/
theorem binAnd_denote
    {u : Com jasminDialect (mapCtx ΓbodyBin) (mapTy (CryptoTy.memref N))}
    (hupd : frontLoopBodyJ (accCTy := .memref N) vmBin "out" (binBody .SAnd) = some u)
    (a b acc : Fin N → BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    JLoopBodyN.denote (accTy := mapTy (CryptoTy.memref N))
        (invTys := mapCtx [CryptoTy.memref N, CryptoTy.memref N]) ⟨n, u⟩
        (.cons a (.cons b .nil)) acc
      = logicFold (fun x y => x &&& y) a b n acc :=
  binFold_denote _ .SAnd (fun hx hy => lower_and_vv hx hy) (fun _ => rfl) binAndBody_covered
    hupd a b acc n hn

/-- The exclusive-or body. -/
theorem binXor_denote
    {u : Com jasminDialect (mapCtx ΓbodyBin) (mapTy (CryptoTy.memref N))}
    (hupd : frontLoopBodyJ (accCTy := .memref N) vmBin "out" (binBody .SXor) = some u)
    (a b acc : Fin N → BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    JLoopBodyN.denote (accTy := mapTy (CryptoTy.memref N))
        (invTys := mapCtx [CryptoTy.memref N, CryptoTy.memref N]) ⟨n, u⟩
        (.cons a (.cons b .nil)) acc
      = logicFold (fun x y => x ^^^ y) a b n acc :=
  binFold_denote _ .SXor (fun hx hy => lower_xor_vv hx hy) (fun _ => rfl) binXorBody_covered
    hupd a b acc n hn

/-- The disjunction body, `(a XOR b) XOR (a AND b)`. -/
theorem binIor_denote
    {u : Com jasminDialect (mapCtx ΓbodyBin) (mapTy (CryptoTy.memref N))}
    (hupd : frontLoopBodyJ (accCTy := .memref N) vmBin "out"
      (binBody (fun x y => .SXor (.SXor x y) (.SAnd x y))) = some u)
    (a b acc : Fin N → BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    JLoopBodyN.denote (accTy := mapTy (CryptoTy.memref N))
        (invTys := mapCtx [CryptoTy.memref N, CryptoTy.memref N]) ⟨n, u⟩
        (.cons a (.cons b .nil)) acc
      = logicFold (fun x y => x ||| y) a b n acc :=
  binFold_denote _ _ (fun hx hy => lower_ior_vv hx hy (by decide) (by decide))
    (fun β => MpnLogicalFrontEmit.iorSE_evalBV β (sv "ai") (sv "bi")) binIorBody_covered
    hupd a b acc n hn

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinFrontDenote
