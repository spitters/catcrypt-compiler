/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# The emit weld: an ascent correspondence read at the emit leg's output word

The ascent calculus (`Ascent/Corres.lean`) proves the **abstraction** leg
`semScalar c → clean ZMod 2^64 spec` via `Corres SR P fa c`. The **emit** leg
`rustToJasminCom_endToEnd_topLevel_unconditional` proves
`jcom.denote … = ctTransTy (tracked output word)` for the `Com jasminDialect`
program `jcom` the pipeline produces. `Corres` alone says nothing about `jcom`.

This module joins the two. The legs share one seam — the denotation
`semScalar c env = some env'`:

* the emit leg reads the tracked output word `val` out of `env'` at `name`
  (`hVal`) and returns `denote = ctTransTy val`;
* the ascent leg's state relation `SRword env' (fa a₀)` says that same slot's
  word encodes the clean spec value `fa a₀ name` (`wEnc val = fa a₀ name`).

The weld stated for an abstract emit map composes them: from a `Corres SRword P fa c`
result run at a `SRword`-populated entry `env₀` and the emit equation `hEmit`, taken
as a hypothesis, it concludes `hEmit` together with `wEnc val = fa a₀ name`.
`keystone_emit` discharges `hEmit` with
`rustToJasminCom_endToEnd_topLevel_unconditional`.

## The satisfiability seam (why the closed-kernel adapter is needed)

`SRword env₀ a₀` binds **every** name (like `EnvRel`), so `env₀ ≠ (fun _ => none)`;
the emit leg's `hSem` uses the empty entry env `fun _ => none`. The two runs use
*different* entry envs. For a **closed** straight-line kernel the tracked output
at a written `name` is a fixed word independent of the entry env, so the two runs
agree there: that is the adapter `hAgree`, discharged by `rfl` for a concrete
closed kernel (see `keystone_setScalar`). This is the *satisfiable* route — the
naive attempt to run `Corres` directly at the empty entry env is vacuous
(`SRword (fun _ => none) a` is false), exactly the `EnvRel`/`ConsistentS` clash
recorded in `RustExecSemScalarBridge`.

## Upward welding

`welding` takes the `RustExec` run of `c` as the premise `hExec` of the emit leg.
A source simulation supplies such a run from an `ImpExpr` evaluation;
`SourceBridge.welding_program` states the weld with `hExec` supplied by the
program-level simulation `haxToLowCT_simulates_program`. hax-lean's
`pipeline_correct` (`HaxLean/Pipeline.lean`) relates a raw `ImpExpr` to its
pipeline output, one level above; `PipelineWeld` uses it.
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

/-! ## The emit weld, abstract in the emit map -/

/-- From an ascent correspondence `Corres SRword P fa c` run at a
    `SRword`-populated entry `(env₀, a₀)`, the emit equation `hEmit`
    (`jdenote = Emit val`) taken as a hypothesis, and the closed-kernel adapter
    `hAgree` (the `env₀`-run leaves `val` at `name`), conclude both the emit
    equation and that the word's clean `ZMod 2^64` spec is `fa a₀ name`. `Emit` is
    abstract; `keystone_emit` instantiates it to `ctTransTy` and discharges
    `hEmit`. -/
theorem corres_emit_weld {β : Type} (Emit : BitVec 64 → β)
    (c : LowCT) (name : String) (val : BitVec 64)
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64)) (jdenote : β)
    (hCorres : Corres SRword P fa c) (hSR : SRword env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩)
    (hEmit : jdenote = Emit val) :
    jdenote = Emit val ∧ wEnc val = fa a₀ name := by
  obtain ⟨env', hSem, hSR'⟩ := hCorres env₀ a₀ hSR hP
  obtain ⟨w, hw, hwenc⟩ := hSR' name
  rw [hAgree env' hSem] at hw
  have hwv : w = val := by have := (Option.some.injEq _ _).mp hw.symm; simpa using this
  subst hwv
  exact ⟨hEmit, hwenc⟩

/-! ## The emit weld with the emit leg discharged -/

/-- **`keystone_emit`.** The emit weld with `hEmit` discharged by the
    end-to-end theorem `rustToJasminCom_endToEnd_topLevel_unconditional`:
    the jasmin program `jcom` denotes to `ctTransTy val`, and `val`'s
    clean `ZMod 2^64` spec is `fa a₀ name`. The `Corres`/`SRword`
    entry and the closed-kernel adapter `hAgree` use the *satisfiable* route
    (a populated entry `env₀`, not the empty env the emit leg runs at). -/
theorem keystone_emit
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
    (hCorres : Corres SRword P fa c) (hSR : SRword env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ wEnc val = fa a₀ name := by
  have hEmit := (rustToJasminCom_endToEnd_topLevel_unconditional
      c o N leafSpec rs rs' env' name w val com jcom
      hCov hTrans hExec hSem hName hVal hRet hCom).2
  exact corres_emit_weld (ctTransTy (t := .sword 64)) c name val fa P env₀ a₀ _
    hCorres hSR hP hAgree hEmit

/-! ## The abstraction side at a literal write

For the concrete closed kernel `RScalarSet name n`, the `Corres`/`SRword`/`P`
entry and the closed-kernel adapter `hAgree` are all dischargeable: `Corres` by
`corres_setScalar`, the entry `SRword` by a constant word env, `P = True`, and
`hAgree` by `rfl`. The abstraction-side hypotheses of the emit weld are therefore
jointly satisfiable. The theorem keeps `Emit` abstract and takes `hEmit` as a
hypothesis; the word reads as the literal `(n : ZMod 2^64)`. -/
theorem keystone_setScalar {β : Type} (Emit : BitVec 64 → β)
    (name : String) (n : Nat) (jdenote : β)
    (hEmit : jdenote = Emit (BitVec.ofNat 64 n)) :
    jdenote = Emit (BitVec.ofNat 64 n) ∧ wEnc (BitVec.ofNat 64 n) = (n : ZMod (2 ^ 64)) := by
  have h : jdenote = Emit (BitVec.ofNat 64 n)
      ∧ wEnc (BitVec.ofNat 64 n)
          = (fun (a : String → ZMod (2 ^ 64)) s =>
              if s = name then (n : ZMod (2 ^ 64)) else a s) (fun _ => wEnc 0) name := by
    let env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩
    refine corres_emit_weld Emit (.RScalarSet name n) name (BitVec.ofNat 64 n) _ (fun _ => True)
      env₀ (fun _ => wEnc 0) jdenote
      (corres_setScalar name n) (fun x => ⟨0, rfl, rfl⟩) trivial ?_ hEmit
    intro e he
    have hstep : semScalar (.RScalarSet name n) env₀
        = some (env₀.upd name (t := .sword 64) (BitVec.ofNat 64 n)) := rfl
    rw [hstep] at he
    obtain rfl : e = env₀.upd name (t := .sword 64) (BitVec.ofNat 64 n) :=
      ((Option.some.injEq _ _).mp he).symm
    simp [SEnvScalar.upd]
  simpa using h

/-! ## Upward welding -/

/-- **`welding`.** `keystone_emit`, with the emit-side `RustExec` premise `hExec`
    listed first among the hypotheses: the premise a source simulation delivers for a kernel
    `e`/`c` (`evalImp bi fuel e env = some (v, env')` and the tower agreement give
    `∃ rs', RustExec N leafSpec c rs rs' ∧ …`). `SourceBridge.welding_program`
    supplies it from the program-level simulation `haxToLowCT_simulates_program`.
    hax-lean's `pipeline_correct` (`denote (pipeline e) = denote e`,
    `HaxLean/Pipeline.lean`) relates the raw `ImpExpr` to its pipeline output one
    level above; `PipelineWeld` uses it. -/
theorem welding
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64))
    (hExec : RustExec N leafSpec c rs rs')       -- from a source simulation
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup name = some ⟨.sword 64, w⟩)
    (hVal : env' name = some ⟨.sword 64, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hCorres : Corres SRword P fa c) (hSR : SRword env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ wEnc val = fa a₀ name :=
  keystone_emit c o N leafSpec rs rs' env' name w val com jcom fa P env₀ a₀
    hCov hTrans hExec hSem hName hVal hRet hCom hCorres hSR hP hAgree

end CatCrypt.Crypto.SecureCompilation.Ascent
