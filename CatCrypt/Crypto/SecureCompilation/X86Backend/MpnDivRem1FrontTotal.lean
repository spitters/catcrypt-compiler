/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref

/-!
# The runtime-trip `mpn_divrem_1` front-success gate, `maxRecDepth`-free

`MpnDivRem1FrontEmit.divRem1RtProgOpt` is `some` because the rolled-loop front
accepts `divLimbBodyLowCT`. This module proves that acceptance the structural
way — a `TransTotal` derivation fed to
`TranslateDialectTotality.frontLoopBodyJ_total` — rather than by reducing the
front on the body under a large `maxRecDepth`.

The body reads the running remainder and dividend limb from two operand arrays,
the accumulator `qp` and the source `up`, and writes the quotient limb and new
remainder back to `qp`, so the derivation runs over a **two-memref**
name-to-type map, supplied by `Dialects.TransFromMemref`.

## Main results

* `divFrontOk` — `(frontLoopBodyJ … vmBody "qp" divLimbBodyLowCT).isSome`, with no
  evaluation of the body's command list.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName notTmp_of_headNe)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys TransTotal SrcTys VmApprox BoundAt boundAt_bind_self boundAt_bind_of_ne
   frontLoopBodyJ_total)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds notE orE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (divLimbBodyLowCT vmBody Gbody NR NU RS qpLoc upLoc)

/-! ## 1. The two-memref map for `mpn_divrem_1` -/

/-- The memref-name map: the accumulator `qp` at the `NR`-word output type, the
    dividend source `up` at the `NU`-word type. -/
def divMem : String → Option CryptoTy := fun x =>
  if x = "qp" then some (.memref NR)
  else if x = "up" then some (.memref NU)
  else none

theorem divMem_qp : divMem "qp" = some (.memref NR) := by decide
theorem divMem_up : divMem "up" = some (.memref NU) := by decide

/-- The loop-body entry word set: the runtime loop index `idx` and the three
    invariants `d`, `dinv` and the limb count `n`. -/
abbrev divB0 : String → Prop := fun y => y = "idx" ∨ y = "d" ∨ y = "dinv" ∨ y = "n"

theorem divB0_srcSet : SrcSet divB0 := by
  rintro x (rfl | rfl | rfl | rfl)
  · exact notTmp_of_headNe rfl (by decide)
  · exact notTmp_of_headNe rfl (by decide)
  · exact notTmp_of_headNe rfl (by decide)
  · exact notTmp_of_headNe rfl (by decide)

theorem divB0_disjoint : ∀ x, divB0 x → divMem x = none := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem divMem_notTmp : ∀ x t, divMem x = some t → ¬ isTmpName x := by
  intro x t hx
  by_cases hqp : x = "qp"
  · exact hqp ▸ notTmp_of_headNe rfl (by decide)
  · by_cases hup : x = "up"
    · exact hup ▸ notTmp_of_headNe rfl (by decide)
    · simp [divMem, hqp, hup] at hx

/-- A `srcClean` high-multiply reads from `R` when both factors do — the
    `SMulHiU` companion of the `TransFromMemref` reads-bound builders. -/
theorem readsFrom_mulHiU {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SMulHiU a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-! ## 2. The `ltuCmds` block is reads-bound -/

/-- **The three-command `ltuCmds` block emits reads-bound commands** from a bound
    operand set: it binds `dst ++ "q"`, `dst ++ "r"` and `dst`, reading only
    names the block already binds. -/
theorem transFromM_ltuCmds {B W : String → Prop} {l : List LowCT} {dst : String}
    {x y : SExpr} (h : TransFromM divMem B W l)
    (hq : ¬ isTmpName (dst ++ "q")) (hqm : divMem (dst ++ "q") = none)
    (hr : ¬ isTmpName (dst ++ "r")) (hrm : divMem (dst ++ "r") = none)
    (hd : ¬ isTmpName dst) (hdm : divMem dst = none)
    (hx : ReadsFrom W x) (hy : ReadsFrom W y) :
    TransFromM divMem B (fun z => ((W z ∨ z = dst ++ "q") ∨ z = dst ++ "r") ∨ z = dst)
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

theorem vmApprox_div : VmApprox (nameTysM divMem divB0) vmBody := by
  intro x t hx
  by_cases hqp : x = "qp"
  · subst hqp
    rw [nameTysM_mem divMem_qp] at hx
    obtain rfl := (Option.some.inj hx).symm
    exact boundAt_bind_self _ "qp" (.memref NR)
  · by_cases hup : x = "up"
    · subst hup
      rw [nameTysM_mem divMem_up] at hx
      obtain rfl := (Option.some.inj hx).symm
      exact boundAt_bind_of_ne "qp" (.memref NR) (by decide)
        (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
          (boundAt_bind_of_ne "d" (.sword 64) (by decide)
            (boundAt_bind_of_ne "dinv" (.sword 64) (by decide)
              (boundAt_bind_of_ne "n" (.sword 64) (by decide)
                (boundAt_bind_self _ "up" (.memref NU))))))
    · by_cases hidx : x = "idx"
      · subst hidx
        rw [nameTysM_word (by decide : divMem "idx" = none)
          (show divB0 "idx" from Or.inl rfl)] at hx
        obtain rfl := (Option.some.inj hx).symm
        exact boundAt_bind_of_ne "qp" (.memref NR) (by decide)
          (boundAt_bind_self _ "idx" (.sword 64))
      · by_cases hd : x = "d"
        · subst hd
          rw [nameTysM_word (by decide : divMem "d" = none)
            (show divB0 "d" from Or.inr (Or.inl rfl))] at hx
          obtain rfl := (Option.some.inj hx).symm
          exact boundAt_bind_of_ne "qp" (.memref NR) (by decide)
            (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
              (boundAt_bind_self _ "d" (.sword 64)))
        · by_cases hdinv : x = "dinv"
          · subst hdinv
            rw [nameTysM_word (by decide : divMem "dinv" = none)
              (show divB0 "dinv" from Or.inr (Or.inr (Or.inl rfl)))] at hx
            obtain rfl := (Option.some.inj hx).symm
            exact boundAt_bind_of_ne "qp" (.memref NR) (by decide)
              (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
                (boundAt_bind_of_ne "d" (.sword 64) (by decide)
                  (boundAt_bind_self _ "dinv" (.sword 64))))
          · by_cases hn : x = "n"
            · subst hn
              rw [nameTysM_word (by decide : divMem "n" = none)
                (show divB0 "n" from Or.inr (Or.inr (Or.inr rfl)))] at hx
              obtain rfl := (Option.some.inj hx).symm
              exact boundAt_bind_of_ne "qp" (.memref NR) (by decide)
                (boundAt_bind_of_ne "idx" (.sword 64) (by decide)
                  (boundAt_bind_of_ne "d" (.sword 64) (by decide)
                    (boundAt_bind_of_ne "dinv" (.sword 64) (by decide)
                      (boundAt_bind_self _ "n" (.sword 64)))))
            · rw [nameTysM_none (by simp [divMem, hqp, hup])
                (fun h => h.elim hidx (fun h => h.elim hd (fun h => h.elim hdinv hn)))] at hx
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

/-- **The scalar rolled-loop front accepts the runtime-trip `mpn_divrem_1`
    body**: the `(frontLoopBodyJ …).isSome` gate holds structurally, with no
    evaluation of the body's command list and no `maxRecDepth` reduction. -/
theorem divFrontOk :
    (frontLoopBodyJ (accCTy := .memref NR) vmBody "qp" divLimbBodyLowCT).isSome := by
  have hones : ones < 2 ^ 64 := by decide
  have hlit1 : (1 : Nat) < 2 ^ 64 := by decide
  have hlitRS : (RS : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromM divMem divB0 divB0 [] := transFromM_nil (Mem := divMem) divB0
  have h1 := transFromM_snoc (x := "top") h0 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "n" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h2 := transFromM_snoc (x := "j") h1 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "top" rfl (by decide) (by decide))
      (rdVar "idx" rfl (by decide) (by decide)))
  have h3 := transFromM_snoc (x := "rs") h2 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlitRS)
  have h4 := transFromM_snocLoad (d := "u1") (ix := "rs") (mty := .TBytes (8 * NR)) h3
    (notTmp_of_headNe rfl (by decide)) (by decide) divMem_qp (by decide)
  have h5 := transFromM_snocLoad (d := "u0") (ix := "j") (mty := .TBytes (8 * NU)) h4
    (notTmp_of_headNe rfl (by decide)) (by decide) divMem_up (by decide)
  have h6 := transFromM_snoc (x := "ql") h5 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mul (rdVar "dinv" rfl (by decide) (by decide))
      (rdVar "u1" rfl (by decide) (by decide)))
  have h7 := transFromM_snoc (x := "qh") h6 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mulHiU (rdVar "dinv" rfl (by decide) (by decide))
      (rdVar "u1" rfl (by decide) (by decide)))
  have h8 := transFromM_snoc (x := "qla") h7 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "ql" rfl (by decide) (by decide))
      (rdVar "u0" rfl (by decide) (by decide)))
  have h9 := transFromM_ltuCmds (dst := "c0") h8
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "qla" rfl (by decide) (by decide)) (rdVar "ql" rfl (by decide) (by decide))
  have h10 := transFromM_snoc (x := "u1p") h9 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "u1" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h11 := transFromM_snoc (x := "qhb") h10 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_add (rdVar "qh" rfl (by decide) (by decide))
        (rdVar "u1p" rfl (by decide) (by decide)))
      (rdVar "c0" rfl (by decide) (by decide)))
  have h12 := transFromM_snoc (x := "p") h11 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_mul (rdVar "qhb" rfl (by decide) (by decide))
      (rdVar "d" rfl (by decide) (by decide)))
  have h13 := transFromM_snoc (x := "r") h12 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "u0" rfl (by decide) (by decide))
      (rdVar "p" rfl (by decide) (by decide)))
  have h14 := transFromM_ltuCmds (dst := "c1") h13
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "qla" rfl (by decide) (by decide)) (rdVar "r" rfl (by decide) (by decide))
  have h15 := transFromM_snoc (x := "m1") h14 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_xor (rdVar "c1" rfl (by decide) (by decide))
        (readsFrom_lit hones)) (readsFrom_lit hlit1))
  have h16 := transFromM_snoc (x := "qhc") h15 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "qhb" rfl (by decide) (by decide))
      (rdVar "m1" rfl (by decide) (by decide)))
  have h17 := transFromM_snoc (x := "ra") h16 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "r" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "m1" rfl (by decide) (by decide))
        (rdVar "d" rfl (by decide) (by decide))))
  have h18 := transFromM_ltuCmds (dst := "c2") h17
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "ra" rfl (by decide) (by decide)) (rdVar "d" rfl (by decide) (by decide))
  have h19 := transFromM_snoc (x := "c3") h18 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "c2" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h20 := transFromM_snoc (x := "m3") h19 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (readsFrom_xor (rdVar "c3" rfl (by decide) (by decide))
        (readsFrom_lit hones)) (readsFrom_lit hlit1))
  have h21 := transFromM_snoc (x := "qout") h20 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_add (rdVar "qhc" rfl (by decide) (by decide))
      (rdVar "c3" rfl (by decide) (by decide)))
  have h22 := transFromM_snoc (x := "rout") h21 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "ra" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "m3" rfl (by decide) (by decide))
        (rdVar "d" rfl (by decide) (by decide))))
  have h23 := transFromM_snocStore (m := "qp") (ix := "j") (s := "qout")
    (mty := .TBytes (8 * NR)) h22
    (notTmp_of_headNe rfl (by decide)) divMem_qp rfl (by decide) (by decide)
  have h24 := transFromM_snocStore (m := "qp") (ix := "rs") (s := "rout")
    (mty := .TBytes (8 * NR)) h23
    (notTmp_of_headNe rfl (by decide)) divMem_qp rfl (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ :=
    h24 divB0 divB0_srcSet divB0_disjoint (fun _ h => h)
  have hT : TransTotal (nameTysM divMem divB0) divLimbBodyLowCT (nameTysM divMem D) :=
    transSteps_seqAll hts
  exact frontLoopBodyJ_total vmBody "qp" divLimbBodyLowCT hT
    (srcTys_nameTysM divMem_notTmp divB0_srcSet) vmApprox_div (nameTysM_mem divMem_qp)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontTotal
