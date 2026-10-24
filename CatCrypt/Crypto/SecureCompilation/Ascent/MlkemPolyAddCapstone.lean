/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemFieldLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge

/-!
# The `ZMod 3329` emit weld for an ML-KEM coefficient value

`Ascent.EmitBridge` welds the *word* ascent (`Corres SRword`) to the emit leg,
concluding `jcom.denote … = ctTransTy val ∧ wEnc val = fa a₀ name` for the
`ZMod 2^64` word spec. This module states the **`ZMod 3329` counterpart**
(`keystone_fq` / `keystone_emit_fq`): given the heterogeneous coefficient
correspondence `CorresH SRfqCanon SRfqVal` (`Ascent.MlkemFieldLeaf`), the jasmin
program denotes to `ctTransTy val` with `fqEnc val = fa a₀ name` the clean
`ZMod 3329` coefficient spec.

The emit leg is the same `rustToJasminCom_endToEnd_topLevel_unconditional`; it does
not depend on which value abstraction reads the tracked output word `val`. Only the
abstraction seam differs: `fqEnc val` is pinned through the value-only output
relation `SRfqVal` instead of `wEnc val` through `SRword`.

## Main results

* `keystone_fq` — the weld abstract in the emit map, with the emit equation `hEmit`
  as a hypothesis; `keystone_emit_fq` — the weld with `hEmit` discharged by the emit
  leg. The package contains no instance of `keystone_emit_fq`.
* `corres_setScalar_fq` — the literal-coefficient leaf (`CorresH SRfqCanon SRfqVal`).
* `keystone_setScalar_fq` — `keystone_fq` at a canonical literal coefficient
  `n < 3329`: the abstraction-side hypotheses are discharged, `hEmit` remains a
  hypothesis, and the word reads as `(n : ZMod 3329)`.
* `corresH_seq`, `polyAddCoeff_corres` — heterogeneous sequencing and the ascent leg
  of one `poly_add` coefficient step.

The whole-polynomial correspondence `polyAdd_fold_corres` is in
`Ascent/MlkemPolyFoldCorres.lean`; no theorem welds it to the emit leg.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap RustStateInterp)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The `ZMod 3329` emit weld, abstract in the emit map -/

/-- **`keystone_fq`.** The emit weld of `EmitBridge` at the coefficient relations.
    From the heterogeneous coefficient correspondence `CorresH SRfqCanon SRfqVal P fa c`
    run at a canonical entry `(env₀, a₀)`, the closed-kernel adapter `hAgree`, the
    non-temp readout side condition `hName_nt`, and the emit equation `hEmit` taken as
    a hypothesis, conclude the emit equation together with `fqEnc val = fa a₀ name`,
    the word's clean `ZMod 3329` spec. -/
theorem keystone_fq {β : Type} (Emit : BitVec 64 → β)
    (c : LowCT) (name : String) (val : BitVec 64)
    (fa : (String → ZMod 3329) → (String → ZMod 3329))
    (P : (String → ZMod 3329) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod 3329) (jdenote : β)
    (hCorres : CorresH SRfqCanon SRfqVal P fa c) (hSR : SRfqCanon env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩)
    (hName_nt : ¬ isTmpName name)
    (hEmit : jdenote = Emit val) :
    jdenote = Emit val ∧ fqEnc val = fa a₀ name := by
  obtain ⟨env', hSem, hSR'⟩ := hCorres env₀ a₀ hSR hP
  obtain ⟨w, hw, hwenc⟩ := hSR' name hName_nt
  rw [hAgree env' hSem] at hw
  have hwv : w = val := by have := (Option.some.injEq _ _).mp hw.symm; simpa using this
  subst hwv
  exact ⟨hEmit, hwenc⟩

/-- **`keystone_emit_fq`.** `keystone_fq` with `hEmit` discharged by
    `rustToJasminCom_endToEnd_topLevel_unconditional`: the jasmin program
    `jcom` denotes to `ctTransTy val`, and `val`'s clean `ZMod 3329` coefficient spec
    is `fa a₀ name`. The emit-side hypotheses are those of the word weld
    `keystone_emit`. -/
theorem keystone_emit_fq
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (fa : (String → ZMod 3329) → (String → ZMod 3329))
    (P : (String → ZMod 3329) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod 3329)
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hVal : env' name = some ⟨.sword 64, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hCorres : CorresH SRfqCanon SRfqVal P fa c) (hSR : SRfqCanon env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩)
    (hName_nt : ¬ isTmpName name) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ fqEnc val = fa a₀ name := by
  have hEmit := (rustToJasminCom_endToEnd_topLevel_unconditional
      c o N leafSpec rs rs' env' name w val com jcom
      hCov hTrans hExec hSem hName hVal hRet hCom).2
  exact keystone_fq (ctTransTy (t := .sword 64)) c name val fa P env₀ a₀ _
    hCorres hSR hP hAgree hName_nt hEmit

/-! ## The literal-coefficient leaf and the weld at a literal -/

/-- The literal-coefficient value leaf: `RScalarSet name n` for a canonical literal
    `n < 3329` sets `name` to `(n : ZMod 3329)`, as a `CorresH SRfqCanon SRfqVal`.
    (The input canonicity is untouched by a literal write, so it holds; the output
    is value-only, since a literal need not be re-read canonically downstream.) -/
theorem corres_setScalar_fq (name : String) (n : Nat) (hn : n < 3329) :
    CorresH SRfqCanon SRfqVal (fun _ => True)
      (fun a s => if s = name then (n : ZMod 3329) else a s)
      (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x hnt
  by_cases hx : x = name
  · refine ⟨BitVec.ofNat 64 n, by simp [SEnvScalar.upd, hx], ?_⟩
    show fqEnc (BitVec.ofNat 64 n) = if x = name then (n : ZMod 3329) else a x
    rw [ite_eq_left hx]
    have hlt : n < 2 ^ 64 := lt_of_lt_of_le hn (by norm_num)
    simp only [fqEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · obtain ⟨w, hw, _, hwEnc⟩ := hSR x hnt
    refine ⟨w, by simp [SEnvScalar.upd, hx, hw], ?_⟩
    show fqEnc w = if x = name then (n : ZMod 3329) else a x
    rw [ite_eq_right hx]; exact hwEnc

/-- **`keystone_setScalar_fq`.** For a canonical literal coefficient `n < 3329`
    written to a non-temp `name`, the abstraction-side hypotheses of `keystone_fq`
    (`CorresH`, the canonical entry `SRfqCanon`, `P = True`, the closed-kernel
    adapter `hAgree`) are discharged, and the word reads as `(n : ZMod 3329)`. The
    emit map `Emit` is abstract and the emit equation `hEmit` is a hypothesis, as in
    `keystone_setScalar`. -/
theorem keystone_setScalar_fq {β : Type} (Emit : BitVec 64 → β)
    (name : String) (n : Nat) (hn : n < 3329) (hname_nt : ¬ isTmpName name)
    (jdenote : β) (hEmit : jdenote = Emit (BitVec.ofNat 64 n)) :
    jdenote = Emit (BitVec.ofNat 64 n) ∧ fqEnc (BitVec.ofNat 64 n) = (n : ZMod 3329) := by
  let env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩
  have hSR₀ : SRfqCanon env₀ (fun _ => (0 : ZMod 3329)) := by
    intro x _; exact ⟨0, rfl, by decide, by simp [fqEnc]⟩
  have h := keystone_fq Emit (.RScalarSet name n) name (BitVec.ofNat 64 n)
    (fun a s => if s = name then (n : ZMod 3329) else a s) (fun _ => True)
    env₀ (fun _ => (0 : ZMod 3329)) jdenote
    (corres_setScalar_fq name n hn) hSR₀ trivial ?_ hname_nt hEmit
  · refine ⟨h.1, ?_⟩
    have := h.2
    simpa using this
  · intro e he
    have hstep : semScalar (.RScalarSet name n) env₀
        = some (env₀.upd name (t := .sword 64) (BitVec.ofNat 64 n)) := rfl
    rw [hstep] at he
    obtain rfl : e = env₀.upd name (t := .sword 64) (BitVec.ofNat 64 n) :=
      ((Option.some.injEq _ _).mp he).symm
    simp [SEnvScalar.upd]

/-! ## Composing the coefficient leaves — the ascent leg of a `poly_add` step

The word ascent composes its leaves with the homogeneous `corres_seq`. The
coefficient ascent, being heterogeneous, needs the heterogeneous sequencing
`corresH_seq` and a canonical-preserving literal leaf `corres_setScalar_fqCanon`
(so the two literal input writes keep the env canonical up to the add). -/

/-- Heterogeneous sequencing: `corres_seq` for `CorresH`. -/
theorem corresH_seq {AState : Type} {SR1 SR2 SR3 : SEnvScalar → AState → Prop}
    {P Q : AState → Prop} {fa ga : AState → AState} {c₁ c₂ : LowCT}
    (h₁ : CorresH SR1 SR2 P fa c₁) (h₂ : CorresH SR2 SR3 Q ga c₂)
    (hpre : ∀ a, P a → Q (fa a)) :
    CorresH SR1 SR3 P (fun a => ga (fa a)) (.RSeq c₁ c₂) := by
  intro env a hSR hP
  obtain ⟨env₁, hstep₁, hSR₁⟩ := h₁ env a hSR hP
  obtain ⟨env₂, hstep₂, hSR₂⟩ := h₂ env₁ (fa a) hSR₁ (hpre a hP)
  refine ⟨env₂, ?_, hSR₂⟩
  simp only [semScalar, hstep₁, Option.bind_some, hstep₂]

/-- The canonical-preserving literal-coefficient leaf: writing a canonical literal
    `n < 3329` keeps the whole env canonical (`SRfqCanon → SRfqCanon`), so it can
    precede a coefficient add that requires a canonical input. -/
theorem corres_setScalar_fqCanon (name : String) (n : Nat) (hn : n < 3329) :
    CorresH SRfqCanon SRfqCanon (fun _ => True)
      (fun a s => if s = name then (n : ZMod 3329) else a s)
      (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x hnt
  have hlt : n < 2 ^ 64 := lt_of_lt_of_le hn (by norm_num)
  by_cases hx : x = name
  · refine ⟨BitVec.ofNat 64 n, by simp [SEnvScalar.upd, hx], ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact hn
    · show fqEnc (BitVec.ofNat 64 n) = if x = name then (n : ZMod 3329) else a x
      rw [ite_eq_left hx]
      simp only [fqEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · obtain ⟨w, hw, hwlt, hwEnc⟩ := hSR x hnt
    refine ⟨w, by simp [SEnvScalar.upd, hx, hw], hwlt, ?_⟩
    show fqEnc w = if x = name then (n : ZMod 3329) else a x
    rw [ite_eq_right hx]; exact hwEnc

/-- **The ascent leg of a canonical `poly_add` coefficient step.** The closed kernel
    `a0 := 100; b0 := 200; r0 := a0 + b0` (canonical literal inputs, `< 3329`)
    ascends, as one `CorresH SRfqCanon SRfqVal`, to its `ZMod 3329` coefficient spec —
    the two canonical literal writes (`corres_setScalar_fqCanon`) sequenced before the
    coefficient-add leaf (`corres_setExpr_fqAdd`) via `corresH_seq`. It has the shape
    of `feAdd_corres` at the coefficient relations, and is of the form the emit weld
    `keystone_emit_fq` takes as `hCorres`. -/
theorem polyAddCoeff_corres :
    CorresH SRfqCanon SRfqVal (fun _ => True)
      (fun a =>
        (fun a s => if s = "r0" then a "a0" + a "b0" else a s)
          ((fun a s => if s = "b0" then ((200 : Nat) : ZMod 3329) else a s)
            ((fun a s => if s = "a0" then ((100 : Nat) : ZMod 3329) else a s) a)))
      (.RSeq (.RScalarSet "a0" 100)
        (.RSeq (.RScalarSet "b0" 200)
          (.RScalarSetExpr "r0" (.SAdd (.SVar "a0") (.SVar "b0"))))) :=
  corresH_seq (corres_setScalar_fqCanon "a0" 100 (by decide))
    (corresH_seq (corres_setScalar_fqCanon "b0" 200 (by decide))
      (corres_setExpr_fqAdd "a0" "b0" "r0"
        (notTmp_of_short "a0" (by decide)) (notTmp_of_short "b0" (by decide)))
      (fun _ _ => trivial))
    (fun _ _ => trivial)

/-- The composite coefficient spec, read at the output slot `r0`, is the clean
    `ZMod 3329` sum of the two canonical inputs: `(100 : ZMod 3329) + (200 : ZMod 3329)`. -/
theorem polyAddCoeff_at_r0 (a : String → ZMod 3329) :
    (fun a =>
        (fun a s => if s = "r0" then a "a0" + a "b0" else a s)
          ((fun a s => if s = "b0" then ((200 : Nat) : ZMod 3329) else a s)
            ((fun a s => if s = "a0" then ((100 : Nat) : ZMod 3329) else a s) a))) a "r0"
      = ((100 : Nat) : ZMod 3329) + ((200 : Nat) : ZMod 3329) := by
  simp

/-! ## What the coefficient results do not cover

**The emit weld for one coefficient.** `polyAddCoeff_corres` is the ascent leg of the
kernel `a0 := 100; b0 := 200; r0 := a0 + b0`. No theorem in the package supplies the
front and emit facts (`translateDialectControl`, `RustExec`, `semScalar`,
`cryptoDialectToJasminCom`) for this kernel, so `keystone_emit_fq` has no instance.
The front facts of `FeAddEndToEnd` are for the literals `av = 1634760805` and
`bv = 857760878`, which are not canonical (`≥ 3329`).

**The polynomial loop.** `corres_for` (`Ascent.Control`) is homogeneous (one relation
`SR`) and takes an index-independent step. `MlkemPolyFoldCorres` states the
index-dependent loop rule `corres_for_indexed` and the whole-polynomial
correspondence `polyAdd_fold_corres` over an unrolled chain of per-index scalar
names, with the homogeneous mixed relation `SRfqMixed`. A loop over array memory
would read `a[i]`, `b[i]` and write `r[i]` through `RArrLoad` and `RArrStore`
(`corres_arrLoad`, `corres_arrStore`), with an abstract state of `256` coefficients;
no theorem in the package states that loop. -/

end CatCrypt.Crypto.SecureCompilation.Ascent
