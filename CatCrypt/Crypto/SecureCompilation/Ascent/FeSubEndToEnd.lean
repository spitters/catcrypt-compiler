/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge
public import CatCrypt.Crypto.SecureCompilation.Ascent.CapstoneField
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq

/-!
# `feSub` end-to-end: the ascent leg welded to the emit leg, no free hypotheses

This module closes the ascent-plan capstone for a real `feSub`-shape kernel
`r := a - b` over a *closed* straight-line program (the two source words are
first written as literals, then subtracted). Both legs of the pipeline are
discharged with no leftover `Corres`/`RustExec` hypothesis:

* **Emit leg** — the verified front/back pipeline's emitted jasmin program
  `feJcom` denotes to `ctTransTy feVal`, where `feVal` is the word `semScalar`
  leaves at `r0`. Discharged through the SATISFIABLE closed-kernel route
  `rustToJasminCom_endToEnd_topLevel_unconditional` (the `RustExecChaChaAdeq`
  `.get`/`rfl` scaffolding), with the `RustExec` reference run built directly
  from the `scalarSet`/`scalarSetExpr` constructors.
* **Ascent leg** — the ascent correspondence `feSub_ascends` (composed with the
  two literal-write leaves via `corres_seq`) pins `wEnc feVal` to the clean
  `ZMod 2^64` spec `(av : ZMod 2^64) - (bv : ZMod 2^64)`.

## `SRwordNT`, not `SRword`

`EmitBridge.welding` / `keystone_emit` are stated over the *total* word relation
`SRword`. The `RScalarSetExpr` value leaf (`corres_setExpr`, hence `feSub_ascends`)
holds only over the non-temp restriction `SRwordNT`: the LowCT lowering scribbles
the fresh-temp namespace, so the total relation is *not* preserved across an
expression assignment (a source kernel never observes those temps). `SRword`
weakens into `SRwordNT` (`srword_srwordNT`) but not conversely, and
`Corres SRword _ _ (.RScalarSetExpr …)` is unprovable. So this module
uses the faithful `SRwordNT` counterparts `keystone_NT` / `keystone_emit_NT`
(exact copies of the two `EmitBridge` welding theorems with `SRword` replaced by
`SRwordNT` and the extra readout-name non-temp side condition `¬ isTmpName name`,
discharged by `not_isTmp_short`). This is the honest reconciliation of the
`SRword`/`SRwordNT` seam the `welding` structure leaves open for `RScalarSetExpr`
kernels.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

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
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The `SRwordNT` welding theorems -/

/-- **`keystone_NT`.** The `SRword` welding theorem of `EmitBridge` over the
    non-temp restriction `SRwordNT`, which is the honest relation for a
    `RScalarSetExpr` value leaf. Identical proof, plus the extra readout-name
    side condition `¬ isTmpName name` (`SRwordNT` only constrains non-temp
    names). -/
theorem keystone_NT {β : Type} (Emit : BitVec 64 → β)
    (c : LowCT) (name : String) (val : BitVec 64)
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64)) (jdenote : β)
    (hCorres : Corres SRwordNT P fa c) (hSR : SRwordNT env₀ a₀) (hP : P a₀)
    (hNT : ¬ isTmpName name)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩)
    (hEmit : jdenote = Emit val) :
    jdenote = Emit val ∧ wEnc val = fa a₀ name := by
  obtain ⟨env', hSem, hSR'⟩ := hCorres env₀ a₀ hSR hP
  obtain ⟨w, hw, hwenc⟩ := hSR' name hNT
  rw [hAgree env' hSem] at hw
  have hwv : w = val := by have := (Option.some.injEq _ _).mp hw.symm; simpa using this
  subst hwv
  exact ⟨hEmit, hwenc⟩

/-- **`keystone_emit_NT`.** The composed `SRword` welding theorem
    (`EmitBridge.keystone_emit`) over `SRwordNT`: the emit supplier is the real
    end-to-end theorem `rustToJasminCom_endToEnd_topLevel_unconditional`, the
    abstraction leg is an `SRwordNT` `Corres`, and the readout name carries the
    `¬ isTmpName name` side condition. -/
theorem keystone_emit_NT
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hVal : env' name = some ⟨.sword 64, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hCorres : Corres SRwordNT P fa c) (hSR : SRwordNT env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩)
    (hNT : ¬ isTmpName name) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ wEnc val = fa a₀ name := by
  have hEmit := (rustToJasminCom_endToEnd_topLevel_unconditional
      c o N leafSpec rs rs' env' name w val com jcom
      hCov hTrans hExec hSem hName hVal hRet hCom).2
  exact keystone_NT (ctTransTy (t := .sword 64)) c name val fa P env₀ a₀ _
    hCorres hSR hP hNT hAgree hEmit

/-! ## The concrete closed `feSub` kernel `r0 := a0 - b0` -/

/-- First literal input `a0`. -/
def av : Nat := 1634760805
/-- Second literal input `b0`. -/
def bv : Nat := 857760878

/-- The subtraction expression `a0 - b0`. -/
def subE : SExpr := .SSub (.SVar "a0") (.SVar "b0")

/-- The closed `feSub` kernel: write the two literal inputs, then subtract. SSA
    form (each write a fresh slot), matching the front's own output. -/
def feSubC : LowCT :=
  .RSeq (.RScalarSet "a0" av)
    (.RSeq (.RScalarSet "b0" bv)
      (.RScalarSetExpr "r0" subE))

theorem subE_srcClean : srcClean subE :=
  ⟨not_isTmp_short "a0" (by decide), not_isTmp_short "b0" (by decide)⟩

theorem subE_arithClean : IsArithClean subE :=
  ⟨not_isTmp_short "a0" (by decide), not_isTmp_short "b0" (by decide)⟩

theorem feSubC_coveredS : IsCoveredS feSubC :=
  .rSeq (.rScalarSet "a0" av)
    (.rSeq (.rScalarSet "b0" bv)
      (.rScalarSetExpr "r0" subE subE_srcClean))

theorem feSubC_covered : IsCoveredSCtl feSubC := .ofStraight feSubC_coveredS

/-! ### The `RustExec` reference run -/

def frs0 : RustState := default
def frs1 : RustState := rsSetScalar frs0 "a0" av
def frs2 : RustState := rsSetScalar frs1 "b0" bv
def frsF : RustState := rsSetScalar frs2 "r0" (subE.eval frs2.rsScalar)

theorem feSubC_exec (N : Nat) (leafSpec : LeafSpec) :
    RustExec N leafSpec feSubC frs0 frsF :=
  .seq _ _ frs0 frs1 frsF (.scalarSet "a0" av frs0)
    (.seq _ _ frs1 frs2 frsF (.scalarSet "b0" bv frs1)
      (.scalarSetExpr "r0" subE frs2))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem fTransSome : (translateDialectControl VarMap.empty feSubC).isSome := by rfl

noncomputable def fO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty feSubC).get fTransSome

theorem fHTrans : translateDialectControl VarMap.empty feSubC = some fO :=
  (Option.some_get fTransSome).symm

theorem fSemSome : (semScalar feSubC (fun _ => none)).isSome := by rfl

noncomputable def fEnv : SEnvScalar := (semScalar feSubC (fun _ => none)).get fSemSome

theorem fHSem : semScalar feSubC (fun _ => none) = some fEnv :=
  (Option.some_get fSemSome).symm

theorem fNameSome : (fO.vm.lookup "r0").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem fNameTy : ((fO.vm.lookup "r0").get fNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `r0`. -/
noncomputable def fW : CVar fO.Γ' (.sword 64) :=
  cast (congrArg (CVar fO.Γ') fNameTy) ((fO.vm.lookup "r0").get fNameSome).2

theorem fHName : fO.vm.lookup "r0" = some ⟨.sword 64, fW⟩ := by decide

theorem fValSome : (fEnv "r0").isSome := by rfl

theorem fValTy : ((fEnv "r0").get fValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `r0`. -/
noncomputable def feVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote fValTy) ((fEnv "r0").get fValSome).2

theorem fHVal : fEnv "r0" = some ⟨.sword 64, feVal⟩ :=
  envSlot_eq_some_sword fEnv "r0" fValSome fValTy feVal rfl

theorem fRetSome : (fO.cont (Com.ret (toVIRVar fW))).isSome := by rfl

noncomputable def fCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (fO.cont (Com.ret (toVIRVar fW))).get fRetSome

theorem fHRet : fO.cont (Com.ret (toVIRVar fW)) = some fCom :=
  (Option.some_get fRetSome).symm

theorem fComSome : (cryptoDialectToJasminCom fCom).isSome := by rfl

noncomputable def feJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom fCom).get fComSome

theorem fHCom : cryptoDialectToJasminCom fCom = some feJcom :=
  (Option.some_get fComSome).symm

/-! ### The abstraction leg: the composed ascent correspondence

`feSub_ascends` for the terminal subtraction, sequenced (`corres_seq`) after the
two literal-write leaves (`corres_setScalar_NT`). The composite abstract map sets
`r0` to `(a0's literal) - (b0's literal)`, i.e. `(av : ZMod 2^64) - (bv : ZMod 2^64)`. -/

/-- The composite abstract map of the closed kernel. -/
def faSub : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a =>
    (fun a =>
      (fun φ s => if s = "r0" then φ "a0" - φ "b0" else φ s)
        ((fun a s => if s = "b0" then ((bv : Nat) : ZMod (2 ^ 64)) else a s) a))
      ((fun a s => if s = "a0" then ((av : Nat) : ZMod (2 ^ 64)) else a s) a)

theorem feSub_corres : Corres SRwordNT (fun _ => True) faSub feSubC := by
  -- Build the composite bottom-up (each factor's `fa` is concrete) so no
  -- higher-order unification against the annotated `faSub` is attempted; the
  -- final `exact` discharges the goal by `beta`-defeq.
  have h := corres_seq SRwordNT (corres_setScalar_NT "a0" av)
    (corres_seq SRwordNT (corres_setScalar_NT "b0" bv)
      (feSub_ascends "a0" "b0" "r0"
        (not_isTmp_short "a0" (by decide)) (not_isTmp_short "b0" (by decide)))
      (fun _ _ => trivial))
    (fun _ _ => trivial)
  exact h

/-- The composite abstract map, evaluated at the output slot, is the clean field
    spec: `(av : ZMod 2^64) - (bv : ZMod 2^64)`. -/
theorem faSub_at_r0 (a : String → ZMod (2 ^ 64)) :
    faSub a "r0" = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  simp [faSub]

/-! ### The `hAgree` closed-kernel adapter

The kernel is closed, so `semScalar feSubC env₀` writes `r0` to a word
independent of the entry `env₀` — the satisfiable route. We run at the constant
zero-word entry, related to the constant zero abstract state. -/

/-- The zero-word entry environment. -/
def env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩

theorem hSR₀ : SRwordNT env₀ (fun _ => (0 : ZMod (2 ^ 64))) :=
  fun _ _ => ⟨0, rfl, by simp [wEnc]⟩

theorem feHAgree :
    ∀ e, semScalar feSubC env₀ = some e → e "r0" = some ⟨.sword 64, feVal⟩ := by
  intro e he
  have hstep : semScalar feSubC env₀
      = some ((semScalar feSubC env₀).get (by rfl)) := (Option.some_get (by rfl)).symm
  rw [hstep] at he
  obtain rfl := (Option.some.injEq _ _).mp he
  rfl

/-! ## The end-to-end theorem -/

/-- **`feSub_endToEnd`.** For the closed `feSub` kernel `r0 := a0 - b0` (literal
    inputs `av`, `bv`), the verified front/back pipeline's emitted jasmin program
    `feJcom` denotes to `ctTransTy feVal`, and the emitted output word's clean
    `ZMod 2^64` spec is exactly `(av : ZMod 2^64) - (bv : ZMod 2^64)` — the ascent
    (`feSub_ascends`) field spec. No free `Corres`/`RustExec` hypothesis: the emit
    leg runs through `rustToJasminCom_endToEnd_topLevel_unconditional`, and the
    ascent leg is welded via `keystone_emit_NT`. -/
theorem feSub_endToEnd (N : Nat) (leafSpec : LeafSpec) :
    feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feVal
      ∧ wEnc feVal = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  have h := keystone_emit_NT feSubC fO N leafSpec frs0 frsF fEnv "r0" fW feVal fCom feJcom
    faSub (fun _ => True) env₀ (fun _ => (0 : ZMod (2 ^ 64)))
    feSubC_covered fHTrans (feSubC_exec N leafSpec) fHSem fHName fHVal fHRet fHCom
    feSub_corres hSR₀ trivial feHAgree (not_isTmp_short "r0" (by decide))
  refine ⟨h.1, ?_⟩
  rw [h.2, faSub_at_r0]

/-! ## Welding the hax-lean source leg (interface)

`feSub_endToEnd` reads from the emitted `feSubC` kernel down to bytes. One level
*up* is the hax-lean source: the extracted `ImpExpr` program `r = a - b`, whose
`evalImp` semantics reach `feSubC` through two cross-repo legs — hax-lean's
`pipeline_correct` (`HaxLean/Pipeline.lean`, denote-preserving `ImpExpr → ImpExpr`,
which builds in `../hax-lean`, not here) and `haxToLowCT_simulates_full`
(`CatCrypt/Crypto/Hax/HaxToLowCTSim_Main_Full.lean`, `evalImp` of the extracted
`ImpExpr` ↔ `RustExec` of the lowered `feSubC`). Fully instantiating that ~14-hypothesis
simulation tower for the concrete feSub `ImpExpr` is out of scope for this module,
so the source→LowCT output identification is taken here as the **explicit interface
hypothesis** `hSourceWord`: the source program's evaluated output word coincides
with the emitted kernel's tracked word `feVal`. That identification is exactly the
conclusion the (cross-repo) simulation tower delivers; chaining it with the
already-discharged emit + ascent legs reads from the source output word all the way
to the emitted bytes' clean `ZMod 2^64` subtraction spec. The remaining interface
is precisely `hSourceWord` — `haxToLowCT_simulates_full ∘ pipeline_correct` for the
feSub `ImpExpr`. -/
theorem feSub_source_to_bytes (N : Nat) (leafSpec : LeafSpec)
    (sourceWord : BitVec 64) (hSourceWord : sourceWord = feVal) :
    feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy sourceWord
      ∧ wEnc sourceWord = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  subst hSourceWord
  exact feSub_endToEnd N leafSpec

end CatCrypt.Crypto.SecureCompilation.Ascent

#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.feSub_endToEnd
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.feSub_source_to_bytes
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.keystone_emit_NT
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.feSub_corres
