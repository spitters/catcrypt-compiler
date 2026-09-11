/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
public import CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref

/-!
# The runtime-trip `mpn_cmp` front-success gate, `maxRecDepth`-free

`MpnCmpFrontEmit.cmpRtProgOpt` is `some` because the rolled-loop front accepts
`cmpLimbBodyLowCT`. This module proves that acceptance the structural way — a
`TransTotal` derivation fed to
`TranslateDialectTotality.frontLoopBodyJ_total` — rather than by reducing the
front on the body under a large `maxRecDepth`.

The body reads two operand arrays `ap` / `bp` and writes the one-word result
array `rp`, so the derivation runs over a **three-memref** name-to-type map,
supplied by `Dialects.TransFromMemref`.

## Main results

* `cmpFrontOk` — `(frontLoopBodyJ … vmBody "rp" cmpLimbBodyLowCT).isSome`, with no
  evaluation of the body's command list.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys TransTotal SrcTys VmApprox BoundAt boundAt_bind_self boundAt_bind_of_ne
   frontLoopBodyJ_total)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds notE orE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpLimbBodyLowCT vmBody Gbody NR NU apLoc bpLoc rpLoc)

/-! ## 1. The three-memref map for `mpn_cmp` -/

/-- The memref-name map: `rp` at the one-word result type, `ap` / `bp` at the
    `NU`-word operand type. -/
def cmpMem : String → Option CryptoTy := fun x =>
  if x = "rp" then some (.memref NR)
  else if x = "ap" then some (.memref NU)
  else if x = "bp" then some (.memref NU)
  else none

theorem cmpMem_rp : cmpMem "rp" = some (.memref NR) := by decide
theorem cmpMem_ap : cmpMem "ap" = some (.memref NU) := by decide
theorem cmpMem_bp : cmpMem "bp" = some (.memref NU) := by decide

/-- The loop-body entry word set: the runtime loop index `idx` and the limb
    count `n`. -/
abbrev cmpB0 : String → Prop := fun y => y = "idx" ∨ y = "n"

theorem cmpB0_srcSet : SrcSet cmpB0 := by
  rintro x (rfl | rfl)
  · exact notTmp_of_headNe rfl (by decide)
  · exact notTmp_of_headNe rfl (by decide)

theorem cmpB0_disjoint : ∀ x, cmpB0 x → cmpMem x = none := by
  rintro x (rfl | rfl) <;> decide

theorem cmpMem_notTmp : ∀ x t, cmpMem x = some t → ¬ isTmpName x := by
  intro x t hx
  by_cases hrp : x = "rp"
  · exact hrp ▸ notTmp_of_headNe rfl (by decide)
  · by_cases hap : x = "ap"
    · exact hap ▸ notTmp_of_headNe rfl (by decide)
    · by_cases hbp : x = "bp"
      · exact hbp ▸ notTmp_of_headNe rfl (by decide)
      · simp [cmpMem, hrp, hap, hbp] at hx

/-! ## 2. The `ltuCmds` block is reads-bound -/

/-- **The three-command `ltuCmds` block emits reads-bound commands** from a bound
    operand set: it binds `dst ++ "q"`, `dst ++ "r"` and `dst`, reading only
    names the block already binds. -/
theorem transFromM_ltuCmds {B W : String → Prop} {l : List LowCT} {dst : String}
    {x y : SExpr} (h : TransFromM cmpMem B W l)
    (hq : ¬ isTmpName (dst ++ "q")) (hqm : cmpMem (dst ++ "q") = none)
    (hr : ¬ isTmpName (dst ++ "r")) (hrm : cmpMem (dst ++ "r") = none)
    (hd : ¬ isTmpName dst) (hdm : cmpMem dst = none)
    (hx : ReadsFrom W x) (hy : ReadsFrom W y) :
    TransFromM cmpMem B (fun z => ((W z ∨ z = dst ++ "q") ∨ z = dst ++ "r") ∨ z = dst)
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

/-! ## 3. The entry map lower-bounds the loop-body `VarMap` -/

theorem vmApprox_cmp : VmApprox (nameTysM cmpMem cmpB0) vmBody := by
  intro x t hx
  by_cases hrp : x = "rp"
  · subst hrp
    rw [nameTysM_mem cmpMem_rp] at hx
    obtain rfl := (Option.some.inj hx).symm
    exact boundAt_bind_self _ "rp" (.memref NR)
  · by_cases hap : x = "ap"
    · subst hap
      rw [nameTysM_mem cmpMem_ap] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
        (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
          (boundAt_bind_self _ "ap" (.memref NU)))
    · by_cases hbp : x = "bp"
      · subst hbp
        rw [nameTysM_mem cmpMem_bp] at hx
        obtain rfl := (Option.some.inj hx).symm
        exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
          (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
            (boundAt_bind_of_ne "ap" (.memref NU) (by decide)
              (boundAt_bind_self _ "bp" (.memref NU))))
      · by_cases hidx : x = "idx"
        · subst hidx
          rw [nameTysM_word (by decide : cmpMem "idx" = none)
            (show cmpB0 "idx" from Or.inl rfl)] at hx
          obtain rfl := (Option.some.inj hx).symm
          exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
            (boundAt_bind_self _ "idx" (.sword 64))
        · by_cases hn : x = "n"
          · subst hn
            rw [nameTysM_word (by decide : cmpMem "n" = none)
              (show cmpB0 "n" from Or.inr rfl)] at hx
            obtain rfl := (Option.some.inj hx).symm
            exact boundAt_bind_of_ne "rp" (.memref NR) (by decide)
              (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
                (boundAt_bind_of_ne "ap" (.memref NU) (by decide)
                  (boundAt_bind_of_ne "bp" (.memref NU) (by decide)
                    (boundAt_bind_self _ "n" (.sword 64)))))
          · rw [nameTysM_none (by simp [cmpMem, hrp, hap, hbp])
              (fun h => h.elim hidx hn)] at hx
            simp at hx

/-! ## 4. The reads-bound derivation and the front-success gate -/

/-- A `TransSteps` walk of a list is a `TransTotal` derivation of its `seqAll`
    sequencing. -/
theorem transSteps_seqAll : ∀ {l : List LowCT} {σ σ' : NameTys},
    TransSteps σ l σ' → TransTotal σ (seqAll l) σ'
  | [], _, _, h => by cases h; exact .rSkip
  | [_], _, _, h => by
      cases h with
      | cons hc ht => cases ht; exact hc
  | _ :: _ :: _, _, _, h => by
      cases h with
      | cons hc ht => exact .rSeq hc (transSteps_seqAll ht)

/-- A pinned scalar read from a bound name. -/
def rdVar {R : String → Prop} (nm : String) {c : Char} {t : List Char}
    (hh : nm.toList = c :: t) (hc : c ≠ '_') (hm : R nm) : ReadsFrom R (sv nm) :=
  readsFrom_var (x := nm) (notTmp_of_headNe hh hc) hm

/-- **The scalar rolled-loop front accepts the runtime-trip `mpn_cmp` body**: the
    `(frontLoopBodyJ …).isSome` gate holds structurally, with no evaluation of the
    body's command list and no `maxRecDepth` reduction. -/
theorem cmpFrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "rp" cmpLimbBodyLowCT).isSome := by
  have hlit1 : (1 : Nat) < 2 ^ 64 := by decide
  have hlit0 : (0 : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromM cmpMem cmpB0 cmpB0 [] := transFromM_nil (Mem := cmpMem) cmpB0
  have h1 := transFromM_snoc (x := "top") h0 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "n" rfl (by decide) (Or.inr rfl)) (readsFrom_lit hlit1))
  have h2 := transFromM_snoc (x := "j") h1 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "top" rfl (by decide) (by decide))
      (rdVar "idx" rfl (by decide) (by decide)))
  have h3 := transFromM_snoc (x := "z") h2 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlit0)
  have h4 := transFromM_snocLoad (d := "x") (ix := "j") (mty := .TBytes (8 * NU)) h3
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_ap (by decide)
  have h5 := transFromM_snocLoad (d := "y") (ix := "j") (mty := .TBytes (8 * NU)) h4
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_bp (by decide)
  have h6 := transFromM_snocLoad (d := "prev") (ix := "z") (mty := .TBytes (8 * NR)) h5
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_rp (by decide)
  have h7 := transFromM_ltuCmds (dst := "lt") h6
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "x" rfl (by decide) (by decide)) (rdVar "y" rfl (by decide) (by decide))
  have h8 := transFromM_ltuCmds (dst := "gt") h7
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "y" rfl (by decide) (by decide)) (rdVar "x" rfl (by decide) (by decide))
  have h9 := transFromM_snoc (x := "step") h8 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "gt" rfl (by decide) (by decide))
      (rdVar "lt" rfl (by decide) (by decide)))
  have h10 := transFromM_ltuCmds (dst := "nz") h9
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlit0) (rdVar "prev" rfl (by decide) (by decide))
  have h11 := transFromM_snoc (x := "keep") h10 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "nz" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h12 := transFromM_snoc (x := "dif") h11 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "step" rfl (by decide) (by decide))
      (rdVar "prev" rfl (by decide) (by decide)))
  have h13 := transFromM_snoc (x := "out") h12 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "prev" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "keep" rfl (by decide) (by decide))
        (rdVar "dif" rfl (by decide) (by decide))))
  have h14 := transFromM_snocStore (m := "rp") (ix := "z") (s := "out")
    (mty := .TBytes (8 * NR)) h13
    (notTmp_of_headNe rfl (by decide)) cmpMem_rp rfl (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ :=
    h14 cmpB0 cmpB0_srcSet cmpB0_disjoint (fun _ h => h)
  have hT : TransTotal (nameTysM cmpMem cmpB0) cmpLimbBodyLowCT (nameTysM cmpMem D) :=
    transSteps_seqAll hts
  exact frontLoopBodyJ_total vmBody "rp" cmpLimbBodyLowCT hT
    (srcTys_nameTysM cmpMem_notTmp cmpB0_srcSet) vmApprox_cmp (nameTysM_mem cmpMem_rp)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal
