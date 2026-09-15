/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote

/-!
# The front-compiled `mpn_divrem_1` limb body is an `ArrMemN` member

`FrontLoopBodyArrMemNWalk.frontLoopBodyJ_arrMemN_of_judged` reduces
`ArrMemN divUpdate` to a `TransArrN` derivation of the `mpn_divrem_1` limb body
over the two-memref name-to-type map, together with the entry-map / accumulator
facts already established for the front-success gate.

The derivation is the memref-typed twin of `MpnDivRem1FrontTotal.divFrontOk`,
assembled through the `TransFromArr` combinator layer of `MpnCmpArrMemN` with
`TransArrN` in place of `TransTotal`. The body reads the running remainder and
dividend limb from the accumulator `qp` and the source `up`, and writes the
quotient limb and new remainder back to `qp`.

## Main results

* `divLimbBody_transArrN` — `TransArrN (nameTysM divMem divB0) divLimbBodyLowCT`
  to a map of the same shape.
* `divUpdate_arrMemN` — the front-compiled `mpn_divrem_1` limb body is a member of
  the array-returning stack-memory fragment `ArrMemN`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1ArrMemN

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName notTmp_of_headNe)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys SrcTys VmApprox)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk
  (TransArrN frontLoopBodyJ_arrMemN_of_judged)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal
  (divMem divMem_qp divMem_up divB0 divB0_srcSet divB0_disjoint divMem_notTmp
   vmApprox_div)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds notE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (divLimbBodyLowCT vmBody NR NU RS)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote (divUpdate divUpdate_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-- A `srcClean` high-multiply reads from `R` when both factors do. -/
theorem readsFrom_mulHiU {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SMulHiU a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-- A pinned scalar read from a bound name. -/
def rdVar {R : String → Prop} (nm : String) {c : Char} {t : List Char}
    (hh : nm.toList = c :: t) (hc : c ≠ '_') (hm : R nm) : ReadsFrom R (sv nm) :=
  readsFrom_var (x := nm) (notTmp_of_headNe hh hc) hm

/-- **The memref-typed reads-bound walk accepts the `mpn_divrem_1` limb body.** The
    array-op arms carry the memref-cell typing, refining the front-success gate's
    `TransTotal` derivation to `TransArrN`, with no reduction of the body command
    list. -/
theorem divLimbBody_transArrN :
    ∃ D : String → Prop,
      TransArrN (nameTysM divMem divB0) divLimbBodyLowCT (nameTysM divMem D) := by
  have hones : ones < 2 ^ 64 := by decide
  have hlit1 : (1 : Nat) < 2 ^ 64 := by decide
  have hlitRS : (RS : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromArr divMem divB0 divB0 [] := transFromArr_nil (Mem := divMem) divB0
  have h1 := transFromArr_snoc (x := "top") h0 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "n" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h2 := transFromArr_snoc (x := "j") h1 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "top" rfl (by decide) (by decide))
      (rdVar "idx" rfl (by decide) (by decide)))
  have h3 := transFromArr_snoc (x := "rs") h2 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlitRS)
  have h4 := transFromArr_snocLoad (d := "u1") (ix := "rs") (mty := .TBytes (8 * NR)) h3
    (notTmp_of_headNe rfl (by decide)) (by decide) divMem_qp (by decide)
  have h5 := transFromArr_snocLoad (d := "u0") (ix := "j") (mty := .TBytes (8 * NU)) h4
    (notTmp_of_headNe rfl (by decide)) (by decide) divMem_up (by decide)
  have h6 := transFromArr_snoc (x := "ql") h5 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mul (rdVar "dinv" rfl (by decide) (by decide))
      (rdVar "u1" rfl (by decide) (by decide)))
  have h7 := transFromArr_snoc (x := "qh") h6 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mulHiU (rdVar "dinv" rfl (by decide) (by decide))
      (rdVar "u1" rfl (by decide) (by decide)))
  have h8 := transFromArr_snoc (x := "qla") h7 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "ql" rfl (by decide) (by decide))
      (rdVar "u0" rfl (by decide) (by decide)))
  have h9 := transFromArr_ltuCmds (dst := "c0") h8
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "qla" rfl (by decide) (by decide)) (rdVar "ql" rfl (by decide) (by decide))
  have h10 := transFromArr_snoc (x := "u1p") h9 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "u1" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h11 := transFromArr_snoc (x := "qhb") h10 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_add (rdVar "qh" rfl (by decide) (by decide))
        (rdVar "u1p" rfl (by decide) (by decide)))
      (rdVar "c0" rfl (by decide) (by decide)))
  have h12 := transFromArr_snoc (x := "p") h11 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mul (rdVar "qhb" rfl (by decide) (by decide))
      (rdVar "d" rfl (by decide) (by decide)))
  have h13 := transFromArr_snoc (x := "r") h12 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "u0" rfl (by decide) (by decide))
      (rdVar "p" rfl (by decide) (by decide)))
  have h14 := transFromArr_ltuCmds (dst := "c1") h13
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "qla" rfl (by decide) (by decide)) (rdVar "r" rfl (by decide) (by decide))
  have h15 := transFromArr_snoc (x := "m1") h14 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_xor (rdVar "c1" rfl (by decide) (by decide))
        (readsFrom_lit hones)) (readsFrom_lit hlit1))
  have h16 := transFromArr_snoc (x := "qhc") h15 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "qhb" rfl (by decide) (by decide))
      (rdVar "m1" rfl (by decide) (by decide)))
  have h17 := transFromArr_snoc (x := "ra") h16 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "r" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "m1" rfl (by decide) (by decide))
        (rdVar "d" rfl (by decide) (by decide))))
  have h18 := transFromArr_ltuCmds (dst := "c2") h17
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "ra" rfl (by decide) (by decide)) (rdVar "d" rfl (by decide) (by decide))
  have h19 := transFromArr_snoc (x := "c3") h18 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "c2" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h20 := transFromArr_snoc (x := "m3") h19 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_xor (rdVar "c3" rfl (by decide) (by decide))
        (readsFrom_lit hones)) (readsFrom_lit hlit1))
  have h21 := transFromArr_snoc (x := "qout") h20 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "qhc" rfl (by decide) (by decide))
      (rdVar "c3" rfl (by decide) (by decide)))
  have h22 := transFromArr_snoc (x := "rout") h21 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "ra" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "m3" rfl (by decide) (by decide))
        (rdVar "d" rfl (by decide) (by decide))))
  have h23 := transFromArr_snocStore (m := "qp") (ix := "j") (s := "qout")
    (mty := .TBytes (8 * NR)) h22
    (notTmp_of_headNe rfl (by decide)) divMem_qp rfl (by decide) (by decide)
  have h24 := transFromArr_snocStore (m := "qp") (ix := "rs") (s := "rout")
    (mty := .TBytes (8 * NR)) h23
    (notTmp_of_headNe rfl (by decide)) divMem_qp rfl (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ :=
    h24 divB0 divB0_srcSet divB0_disjoint (fun _ h => h)
  refine ⟨D, ?_⟩
  exact transStepsArr_seqAll hts

/-- **The front-compiled `mpn_divrem_1` limb body is an `ArrMemN` member.** Feeds
    the memref-typed derivation of the body to `frontLoopBodyJ_arrMemN_of_judged`
    at the output array `qp`, with no reduction of the body command list. -/
theorem divUpdate_arrMemN : ArrMemN divUpdate := by
  obtain ⟨D, hT⟩ := divLimbBody_transArrN
  exact frontLoopBodyJ_arrMemN_of_judged vmBody "qp" divLimbBodyLowCT hT
    (srcTys_nameTysM divMem_notTmp divB0_srcSet) vmApprox_div
    (nameTysM_mem divMem_qp) divUpdate_eq

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1ArrMemN
