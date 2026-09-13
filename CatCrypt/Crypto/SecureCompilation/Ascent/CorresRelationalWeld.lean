/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRelational
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted

/-!
# The `ZMod 251` addition kernel: ascent and front compilation at one program

`CorresRelational` relates the `LowCT` command
`RScalarSetExpr "r" (addMod251Expr "a" "b")` to the abstract `ZMod 251` step
`r := a + b` under the state relation `SRenc encMod251` (`corres_addMod251_abr`).
This module compiles the same command through the front: from the two-slot entry
`VarMap` binding `a` and `b` at `.sword 64`, `translateDialectControl` succeeds,
its continuation applied to the return of `r` succeeds, and the `catCryptDialect`
program lowers to a `Com jasminDialect`. Success is derived from the totality
judgment `TransTotal` (`translateDialectControl_total`); the value of the jasmin
program is `semScalarToJasminCom_denote_eq`.

At the valuation holding `encMod251 (φ "b")` and `encMod251 (φ "a")`, the jasmin
program denotes `encMod251 (φ "a" + φ "b")`, the word the ascent leg places in `r`
from every environment related to `φ` by `SRenc encMod251`. The front-generated
jasmin program and the relational kernel's `Com` `fieldAddMod251Com` are different
programs; they are related here by their denotations at the encoded inputs
(`com_denotes_bop` of `addMod251RealizedKernel`).

## Main definitions

* `CtxAB`, `vmAB`, `valAB` — the two-slot entry context, `VarMap` and encoded
  valuation.
* `envOfVal` — the environment consistent with a `VarMap` and a valuation.

## Main results

* `consistentS_envOfVal` — `envOfVal vm V` is consistent with `vm` and `V`.
* `addMod251_front_weld` — the front translation and the jasmin lowering succeed,
  the jasmin program denotes `encMod251 (φ "a" + φ "b")` and the kernel `Com` at
  the encoded inputs, and the ascent leg from every `SRenc encMod251` environment
  places the same word in `r`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-- The entry context of the two-slot kernel: two `.sword 64` slots. -/
abbrev CtxAB : Ctx := [.sword 64, .sword 64]

/-- The entry `VarMap` binding `b` to slot `0` and `a` to slot `1`. -/
def vmAB : VarMap CtxAB :=
  (VarMap.empty.bind (t := .sword 64) "a").bind (t := .sword 64) "b"

/-- The valuation of `CtxAB` holding the encoded abstract values of `b` and `a`. -/
def valAB (φ : String → ZMod 251) : Ctxt.Valuation (d := catCryptDialect) CtxAB :=
  .cons (encMod251 (φ "b")) (.cons (encMod251 (φ "a")) .nil)

/-- The environment of a `VarMap` and a valuation: each name bound in `vm` holds its
    slot value in `V`, and every other name is unbound. -/
def envOfVal {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    SEnvScalar :=
  fun s => (vm.lookup s).map
    (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))

/-- `envOfVal vm V` is consistent with `vm` and `V`. -/
theorem consistentS_envOfVal {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) : ConsistentS vm V (envOfVal vm V) :=
  fun _ => rfl

/-- The weld of the ascent and the front compilation for the `ZMod 251` addition
    kernel. For every abstract state `φ`:

    * the front translation of `RScalarSetExpr "r" (addMod251Expr "a" "b")` from
      `vmAB` succeeds, tracks `r` at `.sword 64`, its continuation applied to the
      return of `r` succeeds, and the result lowers to a `Com jasminDialect`;
    * the jasmin program denotes `encMod251 (φ "a" + φ "b")` at the valuation
      `valAB φ`;
    * the same word is the denotation of `fieldAddMod251Com`, the `Com` of
      `addMod251RealizedKernel`, at the encoded inputs; the two programs are
      different and agree in denotation;
    * from every environment related to `φ` by `SRenc encMod251`, `semScalar` runs
      the command to an environment related to the abstract step `r := a + b` in
      which `r` holds the denotation of the jasmin program. -/
theorem addMod251_front_weld (φ : String → ZMod 251) :
    ∃ (o : DTransOut CtxAB) (w : CVar o.Γ' (.sword 64))
      (com : Com catCryptDialect CtxAB (.sword 64))
      (jcom : Com jasminDialect (mapCtx CtxAB) (mapTy (.sword 64))),
      translateDialectControl vmAB (.RScalarSetExpr "r" (addMod251Expr "a" "b")) = some o ∧
      o.vm.lookup "r" = some ⟨.sword 64, w⟩ ∧
      o.cont (Com.ret (toVIRVar w)) = some com ∧
      cryptoDialectToJasminCom com = some jcom ∧
      jcom.denote (ctMapValD (valAB φ)) = encMod251 (φ "a" + φ "b") ∧
      jcom.denote (ctMapValD (valAB φ)) =
        Com.denote addMod251RealizedKernel.com
          (.cons (encMod251 (φ "b")) (.cons (encMod251 (φ "a")) .nil)) ∧
      ∀ env : SEnvScalar, SRenc encMod251 env φ →
        ∃ env' : SEnvScalar,
          semScalar (.RScalarSetExpr "r" (addMod251Expr "a" "b")) env = some env' ∧
          SRenc encMod251 env' (fun s => if s = "r" then φ "a" + φ "b" else φ s) ∧
          env' "r" = some ⟨.sword 64, jcom.denote (ctMapValD (valAB φ))⟩ := by
  have ha : ¬ isTmpName "a" := notTmp_of_short "a" (by decide)
  have hb : ¬ isTmpName "b" := notTmp_of_short "b" (by decide)
  have hr : ¬ isTmpName "r" := notTmp_of_short "r" (by decide)
  have hcl : srcClean (addMod251Expr "a" "b") := srcClean_addMod251Expr ha hb
  -- Front success from the totality judgment.
  let σ : NameTys := fun y => if y = "a" ∨ y = "b" then some (.sword 64) else none
  have htot : TransTotal σ (.RScalarSetExpr "r" (addMod251Expr "a" "b"))
      (σ.upd "r" (.sword 64)) := by
    refine .rScalarSetExpr "r" _ hr hcl ?_
    intro y hy
    simp only [addMod251Expr, csub251Expr, sexprVars, List.append_nil, List.nil_append,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hy
    simp only [σ, if_pos hy]
  have hσ : SrcTys σ := by
    intro x hx
    by_cases hab : x = "a" ∨ x = "b"
    · rcases hab with rfl | rfl
      · exact ha
      · exact hb
    · simp only [σ, if_neg hab, Option.isSome_none, Bool.false_eq_true] at hx
  have happ : VmApprox σ vmAB := by
    intro x t hx
    by_cases hab : x = "a" ∨ x = "b"
    · simp only [σ, if_pos hab, Option.some.injEq] at hx
      subst hx
      rcases hab with rfl | rfl
      · exact ⟨.there .here, rfl⟩
      · exact ⟨.here, rfl⟩
    · simp only [σ, if_neg hab, reduceCtorEq] at hx
  obtain ⟨o, htr, happ', hcont⟩ := translateDialectControl_total htot vmAB hσ happ
  obtain ⟨w, hw⟩ := happ' "r" (.sword 64) (by simp only [NameTys.upd, ↓reduceIte])
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar w)) (by rfl)
  obtain ⟨jcom, hjcom⟩ := Option.isSome_iff_exists.mp hlow
  -- The source run from the environment of the entry valuation.
  have hcons := consistentS_envOfVal vmAB (valAB φ)
  have h0a : envOfVal vmAB (valAB φ) "a" = some ⟨.sword 64, encMod251 (φ "a")⟩ := rfl
  have h0b : envOfVal vmAB (valAB φ) "b" = some ⟨.sword 64, encMod251 (φ "b")⟩ := rfl
  let rs : RustState :=
    ⟨fun _ => none, fun y => (envReader (envOfVal vmAB (valAB φ)) y).toNat⟩
  have hEB : EnvBoundOn rs (envOfVal vmAB (valAB φ)) (fun y => y = "a" ∨ y = "b") := by
    rintro x (rfl | rfl) _
    · show envOfVal vmAB (valAB φ) "a" =
        some ⟨.sword 64, BitVec.ofNat 64 (envReader (envOfVal vmAB (valAB φ)) "a").toNat⟩
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h0a
    · show envOfVal vmAB (valAB φ) "b" =
        some ⟨.sword 64, BitVec.ofNat 64 (envReader (envOfVal vmAB (valAB φ)) "b").toNat⟩
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h0b
  have hvb : varsBoundIn (fun y => y = "a" ∨ y = "b") (addMod251Expr "a" "b") := by
    simp only [addMod251Expr, csub251Expr, varsBoundIn, true_or, or_true, and_true]
  obtain ⟨env2, _, _, hsem, _⟩ :=
    semLowerSExpr_ok' rs _ (addMod251Expr "a" "b") (envOfVal vmAB (valAB φ)) 0 hEB hvb hcl
  have hsemc : semScalar (.RScalarSetExpr "r" (addMod251Expr "a" "b"))
      (envOfVal vmAB (valAB φ)) =
      some (env2.upd "r" (t := .sword 64)
        (SExpr.evalBV (envReader (envOfVal vmAB (valAB φ))) (addMod251Expr "a" "b"))) := by
    simp only [semScalar, hsem]
  have hval : (env2.upd "r" (t := .sword 64)
      (SExpr.evalBV (envReader (envOfVal vmAB (valAB φ))) (addMod251Expr "a" "b"))) "r" =
      some ⟨.sword 64, csub251 (encMod251 (φ "a") + encMod251 (φ "b"))⟩ := by
    simp only [SEnvScalar.upd]
    rfl
  have hK : jcom.denote (ctMapValD (valAB φ)) =
      csub251 (encMod251 (φ "a") + encMod251 (φ "b")) :=
    CompilerCorrectnessExtracted.semScalarToJasminCom_denote_eq vmAB _ o (valAB φ)
      (envOfVal vmAB (valAB φ)) _ "r" w _ com jcom
      (.ofStraight (.rScalarSetExpr _ _ hcl)) htr hcons hsemc hw hval hcom hjcom
  have hE : jcom.denote (ctMapValD (valAB φ)) = encMod251 (φ "a" + φ "b") := by
    rw [hK]; exact (encMod251_commutes _ _).symm
  refine ⟨o, w, com, jcom, htr, hw, hcom, hjcom, hE, ?_, ?_⟩
  · rw [hK]; exact (addMod251RealizedKernel.com_denotes_bop _ _).symm
  · intro env hSR
    obtain ⟨env', hstep, hSR'⟩ := corres_addMod251_abr env φ hSR trivial
    refine ⟨env', hstep, hSR', ?_⟩
    rw [hSR' "r" hr]
    simp only [↓reduceIte, hE]

end CatCrypt.Crypto.SecureCompilation.Ascent
