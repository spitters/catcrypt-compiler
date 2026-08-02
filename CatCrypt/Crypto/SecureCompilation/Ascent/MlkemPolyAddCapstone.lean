/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemFieldLeaf
import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge

/-!
# The `ZMod 3329` keystone: an ML-KEM coefficient value ascends to emitted bytes

`Ascent.EmitBridge` welds the *word* ascent (`Corres SRword`) to the emit leg,
concluding `denote(bytes) = ctTransTy val ∧ wEnc val = fa a₀ name` for the
`ZMod 2^64` word spec. This module builds the **`ZMod 3329` counterpart**
(`keystone_fq` / `keystone_emit_fq`): given the heterogeneous coefficient
correspondence `CorresH SRfqCanon SRfqVal` (`Ascent.MlkemFieldLeaf`), the emitted
jasmin bytes denote to `ctTransTy val` with `fqEnc val = fa a₀ name` the clean
`ZMod 3329` coefficient spec.

The emit leg is the SAME `rustToJasminCom_endToEnd_topLevel_unconditional` — it is
agnostic to which value abstraction reads the tracked output word `val`. Only the
abstraction seam changes: instead of pinning `wEnc val` through `SRword`, we pin
`fqEnc val` through the value-only output relation `SRfqVal`.

## What lands here

* `keystone_fq` / `keystone_emit_fq` — the abstract and emit-composed bridges over
  the coefficient relations.
* `corres_setScalar_fq` — the literal-coefficient leaf (`CorresH SRfqCanon SRfqVal`).
* `keystone_setScalar_fq` — a **non-vacuity witness**: for a canonical literal
  coefficient `n < 3329`, the emitted bytes denote to `Emit (ofNat 64 n)` and its
  clean `ZMod 3329` spec is `(n : ZMod 3329)`. This exhibits the coefficient
  keystone's abstraction-side hypotheses as jointly satisfiable — the bridge is not
  vacuous — exactly as `keystone_setScalar` does for the word layer.

## Frontier (see the module-end note)

The full `poly_add` capstone — the 256-coefficient loop composed via `corres_for`,
then welded to bytes — is NOT closed here. The precise obstructions are recorded at
the end of this file.
-/

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

/-! ## The `ZMod 3329` keystone (abstract in the emit map) -/

/-- **`keystone_fq`.** The coefficient analogue of `keystone`. From the heterogeneous
    coefficient correspondence `CorresH SRfqCanon SRfqVal P fa c` run at a canonical
    entry `(env₀, a₀)`, the closed-kernel adapter `hAgree`, and the non-temp readout
    side condition `hName_nt`, conclude the emit equation together with
    `fqEnc val = fa a₀ name` — the emitted word's clean `ZMod 3329` spec. -/
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

/-- **`keystone_emit_fq`.** `keystone_fq` with the emit supplier discharged by the
    real `rustToJasminCom_endToEnd_topLevel_unconditional`: the emitted jasmin program
    `jcom` denotes to `ctTransTy val`, and `val`'s clean `ZMod 3329` coefficient spec
    is `fa a₀ name`. The emit-side data is the standard covered-kernel input, shared
    verbatim with the word keystone `keystone_emit`. -/
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

/-! ## The literal-coefficient leaf and the non-vacuity witness -/

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
    rw [if_pos hx]
    have hlt : n < 2 ^ 64 := lt_of_lt_of_le hn (by norm_num)
    simp only [fqEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · obtain ⟨w, hw, _, hwEnc⟩ := hSR x hnt
    refine ⟨w, by simp [SEnvScalar.upd, hx, hw], ?_⟩
    show fqEnc w = if x = name then (n : ZMod 3329) else a x
    rw [if_neg hx]; exact hwEnc

/-- **`keystone_setScalar_fq` — the coefficient keystone is not vacuous.** For a
    canonical literal coefficient `n < 3329` written to a non-temp `name`, the
    coefficient keystone's abstraction-side hypotheses (`CorresH`, the canonical
    entry `SRfqCanon`, `P = True`, the closed-kernel adapter `hAgree`) are jointly
    dischargeable, and the clean spec value read out is exactly `(n : ZMod 3329)`.
    The emit map `Emit` is abstract (instantiated to `ctTransTy` in
    `keystone_emit_fq`); this exhibits satisfiability, mirroring `keystone_setScalar`. -/
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

/-- Heterogeneous sequencing — the `CorresH` analogue of `corres_seq`. -/
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
      rw [if_pos hx]
      simp only [fqEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · obtain ⟨w, hw, hwlt, hwEnc⟩ := hSR x hnt
    refine ⟨w, by simp [SEnvScalar.upd, hx, hw], hwlt, ?_⟩
    show fqEnc w = if x = name then (n : ZMod 3329) else a x
    rw [if_neg hx]; exact hwEnc

/-- **The ascent leg of a canonical `poly_add` coefficient step.** The closed kernel
    `a0 := 100; b0 := 200; r0 := a0 + b0` (canonical literal inputs, `< 3329`)
    ascends, as one `CorresH SRfqCanon SRfqVal`, to its `ZMod 3329` coefficient spec —
    the two canonical literal writes (`corres_setScalar_fqCanon`) sequenced before the
    coefficient-add leaf (`corres_setExpr_fqAdd`) via `corresH_seq`. This is the
    coefficient analogue of `feAdd_corres`, and the exact ascent input the emit weld
    `keystone_emit_fq` consumes. -/
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

/-! ## Frontier — the two remaining gaps to a closed `poly_add` source→bytes capstone

**(1) The concrete emit weld for one coefficient — mechanical.** `polyAddCoeff_corres`
is the full ascent leg; welding it to emitted bytes is `keystone_emit_fq` fed the
concrete-kernel emit data (`translateDialectControl` / `RustExec` / `semScalar` /
`cryptoDialectToJasminCom` `.get`/`rfl` facts). That scaffolding is exactly
`FeAddEndToEnd`'s ~150 lines, but its literals `av = 1634760805`, `bv = 857760878`
are NOT canonical (`≥ 3329`), so it cannot be reused as-is; a canonical-literal clone
(`a0 := 100; b0 := 200`) is needed. No new theory — a mechanical clone.

**(2) The 256-coefficient loop — genuine new work.** `corres_for`
(`Ascent.Control`) is generic in the state relation, but it is HOMOGENEOUS
(`Corres SR`, one relation) and hardwired to a 64-bit counter (`BitVec.ofNat 64 n`).
An unreduced `poly_add` loop needs the heterogeneous `CorresH` at the loop level
(canonical inputs, non-canonical outputs), i.e. a `corresH_for`, which does not
exist. Beyond that, the loop body reads `a[i]`, `b[i]` and writes `r[i]` through
array load/store, not scalar names: the array-store leaf `corres_arrStore` exists,
but the array-LOAD leaf (`RArrLoad`) is the open dual noted in the Ascent frontier,
and the abstract state would be a `Vector Zq3329 256`, not `String → ZMod 3329`.
Finally, the spike's index-fold lemma `ExtractionTransferSpike.go_update_getElem?`
characterizes `Hax.foldRange.go` over `Array Int` (the extraction's own fold), which
is a DIFFERENT recursion from `semScalar`'s `semRForD` that `corres_for` peels — so
it does not plug into `corres_for` directly; bridging them is part of the same
array/loop tower work. -/

end CatCrypt.Crypto.SecureCompilation.Ascent
