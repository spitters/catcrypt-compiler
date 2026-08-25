/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote

/-!
# The front-compiled `mpn_mul_basecase` inner limb body is an `ArrMemN` member

`FrontLoopBodyArrMemNWalk.frontLoopBodyJ_arrMemN_of_judged` reduces
`ArrMemN bcRowUpdate` to a `TransArrN` derivation of the `mpn_mul_basecase` inner
limb body over the three-memref name-to-type map, together with the entry-map /
accumulator facts already established for the front-success gate.

The derivation is the memref-typed twin of the inner-body coverage in
`MpnMulBasecaseFrontDenote`, assembled through the `TransFromArr` combinator layer
of `MpnCmpArrMemN` with `TransArrN`. The body reads the masked multiplicand limb
from `up`, the row scalar from `vp`, the running carry and destination word from
the accumulator `rp`, forms the widening multiply-add, and writes the low word and
the new carry back to `rp`.

## Main results

* `bcRowBody_transArrN` — `TransArrN (nameTysM bcMem bcB0) rowBodyLowCT` to a map of
  the same shape.
* `bcRowUpdate_arrMemN` — the front-compiled `mpn_mul_basecase` inner limb body is a
  member of the array-returning stack-memory fragment `ArrMemN`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseArrMemN

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys SrcTys VmApprox)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk
  (TransArrN frontLoopBodyJ_arrMemN_of_judged)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote
  (bcMem bcMem_rp bcMem_up bcMem_vp bcB0 bcB0_srcSet bcB0_disjoint bcMem_notTmp
   vmApprox_bc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds notE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (rowBodyLowCT vmBody NR NU NV upLoc vpLoc rpLoc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote (bcRowUpdate bcRowUpdate_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-- A `srcClean` high-multiply reads from `R` when both factors do. -/
private theorem readsFrom_mulHiU {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SMulHiU a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-- A pinned scalar read from a bound name. -/
private def rdVar {R : String → Prop} (nm : String) {c : Char} {t : List Char}
    (hh : nm.toList = c :: t) (hc : c ≠ '_') (hm : R nm) : ReadsFrom R (sv nm) :=
  readsFrom_var (x := nm) (notTmp_of_headNe hh hc) hm

/-- **The memref-typed reads-bound walk accepts the `mpn_mul_basecase` inner limb
    body.** The array-op arms carry the memref-cell typing, refining the inner-body
    coverage to `TransArrN`, with no reduction of the body command list. -/
theorem bcRowBody_transArrN :
    ∃ D : String → Prop,
      TransArrN (nameTysM bcMem bcB0) rowBodyLowCT (nameTysM bcMem D) := by
  have hlit0 : (0 : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromArr bcMem bcB0 bcB0 [] := transFromArr_nil (Mem := bcMem) bcB0
  -- ltuCmds "kb" (sv "t") (sv "un")
  have h1 := transFromArr_ltuCmds (dst := "kb") h0
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "t" rfl (by decide) (by decide)) (rdVar "un" rfl (by decide) (by decide))
  -- msk := 0 - kb
  have h2 := transFromArr_snoc (x := "msk") h1 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (readsFrom_lit hlit0) (rdVar "kb" rfl (by decide) (by decide)))
  -- tm := t & msk
  have h3 := transFromArr_snoc (x := "tm") h2 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_and (rdVar "t" rfl (by decide) (by decide))
      (rdVar "msk" rfl (by decide) (by decide)))
  -- a0 := up[tm]
  have h4 := transFromArr_snocLoad (d := "a0") (ix := "tm") (mty := .TBytes (8 * NU)) h3
    (notTmp_of_headNe rfl (by decide)) (by decide) bcMem_up (by decide)
  -- a := a0 & msk
  have h5 := transFromArr_snoc (x := "a") h4 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_and (rdVar "a0" rfl (by decide) (by decide))
      (rdVar "msk" rfl (by decide) (by decide)))
  -- vv := vp[jd]
  have h6 := transFromArr_snocLoad (d := "vv") (ix := "jd") (mty := .TBytes (8 * NV)) h5
    (notTmp_of_headNe rfl (by decide)) (by decide) bcMem_vp (by decide)
  -- lo := a * vv
  have h7 := transFromArr_snoc (x := "lo") h6 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mul (rdVar "a" rfl (by decide) (by decide))
      (rdVar "vv" rfl (by decide) (by decide)))
  -- hi := mulhi a vv
  have h8 := transFromArr_snoc (x := "hi") h7 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mulHiU (rdVar "a" rfl (by decide) (by decide))
      (rdVar "vv" rfl (by decide) (by decide)))
  -- nc := un + vn
  have h9 := transFromArr_snoc (x := "nc") h8 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "un" rfl (by decide) (by decide))
      (rdVar "vn" rfl (by decide) (by decide)))
  -- cy := rp[nc]
  have h10 := transFromArr_snocLoad (d := "cy") (ix := "nc") (mty := .TBytes (8 * NR)) h9
    (notTmp_of_headNe rfl (by decide)) (by decide) bcMem_rp (by decide)
  -- s1 := lo + cy
  have h11 := transFromArr_snoc (x := "s1") h10 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "lo" rfl (by decide) (by decide))
      (rdVar "cy" rfl (by decide) (by decide)))
  -- ltuCmds "k1" (sv "s1") (sv "lo")
  have h12 := transFromArr_ltuCmds (dst := "k1") h11
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "s1" rfl (by decide) (by decide)) (rdVar "lo" rfl (by decide) (by decide))
  -- pi := jd + t
  have h13 := transFromArr_snoc (x := "pi") h12 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "jd" rfl (by decide) (by decide))
      (rdVar "t" rfl (by decide) (by decide)))
  -- rr := rp[pi]
  have h14 := transFromArr_snocLoad (d := "rr") (ix := "pi") (mty := .TBytes (8 * NR)) h13
    (notTmp_of_headNe rfl (by decide)) (by decide) bcMem_rp (by decide)
  -- s2 := s1 + rr
  have h15 := transFromArr_snoc (x := "s2") h14 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "s1" rfl (by decide) (by decide))
      (rdVar "rr" rfl (by decide) (by decide)))
  -- ltuCmds "k2" (sv "s2") (sv "s1")
  have h16 := transFromArr_ltuCmds (dst := "k2") h15
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "s2" rfl (by decide) (by decide)) (rdVar "s1" rfl (by decide) (by decide))
  -- hc := (hi + k1) + k2
  have h17 := transFromArr_snoc (x := "hc") h16 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_add (rdVar "hi" rfl (by decide) (by decide))
        (rdVar "k1" rfl (by decide) (by decide)))
      (rdVar "k2" rfl (by decide) (by decide)))
  -- rp[pi] := s2
  have h18 := transFromArr_snocStore (m := "rp") (ix := "pi") (s := "s2")
    (mty := .TBytes (8 * NR)) h17
    (notTmp_of_headNe rfl (by decide)) bcMem_rp rfl (by decide) (by decide)
  -- rp[nc] := hc
  have h19 := transFromArr_snocStore (m := "rp") (ix := "nc") (s := "hc")
    (mty := .TBytes (8 * NR)) h18
    (notTmp_of_headNe rfl (by decide)) bcMem_rp rfl (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ :=
    h19 bcB0 bcB0_srcSet bcB0_disjoint (fun _ h => h)
  refine ⟨D, ?_⟩
  exact transStepsArr_seqAll hts

/-- **The front-compiled `mpn_mul_basecase` inner limb body is an `ArrMemN`
    member.** Feeds the memref-typed derivation of the body to
    `frontLoopBodyJ_arrMemN_of_judged` at the output array `rp`, with no reduction
    of the body command list. -/
theorem bcRowUpdate_arrMemN : ArrMemN bcRowUpdate := by
  obtain ⟨D, hT⟩ := bcRowBody_transArrN
  exact frontLoopBodyJ_arrMemN_of_judged vmBody "rp" rowBodyLowCT hT
    (srcTys_nameTysM bcMem_notTmp bcB0_srcSet) vmApprox_bc
    (nameTysM_mem bcMem_rp) bcRowUpdate_eq

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseArrMemN
