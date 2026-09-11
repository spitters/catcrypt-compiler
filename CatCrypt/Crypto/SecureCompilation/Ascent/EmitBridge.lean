/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge

/-!
# The keystone: the ascent abstraction leg discharges the emit leg

The ascent calculus (`Ascent/Corres.lean`) proves the **abstraction** leg
`semScalar c → clean ZMod 2^64 spec` via `Corres SR P fa c`. Every existing
kernel-correctness result instead proves the **emit** leg
`denote(emitted jasmin bytes) = ctTransTy (tracked output word)` via
`rustToJasminCom_endToEnd_topLevel_unconditional`. `Corres` alone touches no
jasmin bytes, so it discharges no emit conclusion on its own.

This module is the bridge. The two legs share one seam — the denotation
`semScalar c env = some env'`:

* the emit leg reads the tracked output word `val` out of `env'` at `name`
  (`hVal`) and returns `denote = ctTransTy val`;
* the ascent leg's state relation `SRword env' (fa a₀)` says that same slot's
  word encodes the clean spec value `fa a₀ name` (`wEnc val = fa a₀ name`).

`keystone` composes them: an abstract `Corres SRword P fa c` result, run at a
`SRword`-populated entry `env₀`, pins `wEnc val = fa a₀ name`, and the emit-leg
output supplies `denote = ctTransTy val`. `keystone_emit` wires the *real*
`rustToJasminCom_endToEnd_topLevel_unconditional` in as the emit supplier.

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

`welding` threads the `RustExec` produced by `haxToLowCT_simulates_full`
(`evalImp` of the extracted `ImpExpr` ↔ `RustExec` of the lowered `LowCT`) into
the emit leg's `hExec`, so the statement reads from the `ImpExpr` denotation down
to the emitted bytes' clean spec. The hax-lean leg `pipeline_correct`
(cross-repo, `../hax-lean`) attaches one level above, rewriting the source
`ImpExpr` that `evalImp` consumes.
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

/-! ## The keystone (abstract in the emit map) -/

/-- **`keystone`.** From an ascent correspondence `Corres SRword P fa c` run at a
    `SRword`-populated entry `(env₀, a₀)` and the emit-leg output `hEmit`
    (`jdenote = Emit val`), together with the closed-kernel adapter `hAgree`
    (the `env₀`-run leaves `val` at `name`), conclude both the emit equation and
    that the emitted word's clean `ZMod 2^64` spec is `fa a₀ name`. `Emit` is
    abstract; it is instantiated to `ctTransTy` in `keystone_emit`. -/
theorem keystone {β : Type} (Emit : BitVec 64 → β)
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

/-! ## The composed keystone (real emit theorem) -/

/-- **`keystone_emit`.** The keystone with the emit supplier discharged by the
    real end-to-end theorem `rustToJasminCom_endToEnd_topLevel_unconditional`:
    the emitted jasmin program `jcom` denotes to `ctTransTy val`, and `val`'s
    clean `ZMod 2^64` spec is `fa a₀ name`. This is the theorem that makes an
    ascent `Corres` result discharge an emit conclusion. The `Corres`/`SRword`
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
  exact keystone (ctTransTy (t := .sword 64)) c name val fa P env₀ a₀ _
    hCorres hSR hP hAgree hEmit

/-! ## Non-vacuity witness for the abstraction/adapter side

For the concrete closed kernel `RScalarSet name n`, the `Corres`/`SRword`/`P`
entry and the closed-kernel adapter `hAgree` are all dischargeable: `Corres` by
`corres_setScalar`, the entry `SRword` by a constant word env, `P = True`, and
`hAgree` by `rfl`. This exhibits that `keystone`'s abstraction-side hypotheses
are jointly satisfiable (the bridge is not vacuous); the emit-side data is the
standard covered-kernel input to `rustToJasminCom_endToEnd_topLevel_unconditional`.
The clean spec value read out is exactly the literal `(n : ZMod 2^64)`. -/
theorem keystone_setScalar {β : Type} (Emit : BitVec 64 → β)
    (name : String) (n : Nat) (jdenote : β)
    (hEmit : jdenote = Emit (BitVec.ofNat 64 n)) :
    jdenote = Emit (BitVec.ofNat 64 n) ∧ wEnc (BitVec.ofNat 64 n) = (n : ZMod (2 ^ 64)) := by
  have h : jdenote = Emit (BitVec.ofNat 64 n)
      ∧ wEnc (BitVec.ofNat 64 n)
          = (fun (a : String → ZMod (2 ^ 64)) s =>
              if s = name then (n : ZMod (2 ^ 64)) else a s) (fun _ => wEnc 0) name := by
    let env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩
    refine keystone Emit (.RScalarSet name n) name (BitVec.ofNat 64 n) _ (fun _ => True)
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

/-- **`welding`.** The emit-side `RustExec` premise `hExec` is exactly the
    conclusion `haxToLowCT_simulates_full` delivers for the kernel `e`/`c`
    (`evalImp bi fuel e env = some (v, env')` and the tower agreement give
    `∃ rs', RustExec N leafSpec c rs rs' ∧ …`). Threading that `RustExec` into
    `keystone_emit` reads the whole chain from the extracted `ImpExpr`'s
    `evalImp` denotation down to the emitted bytes' clean `ZMod 2^64` spec. The
    hax-lean leg `pipeline_correct` (`denote (pipeline e) = denote e`, cross-repo
    in `../hax-lean`) attaches one level *above*: it rewrites the source
    `ImpExpr` that supplies `evalImp e = some (v, env')` for the post-pipeline
    program, and does not build in this repo. -/
theorem welding
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (name : String) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.sword 64))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)))
    (fa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)))
    (P : (String → ZMod (2 ^ 64)) → Prop)
    (env₀ : SEnvScalar) (a₀ : String → ZMod (2 ^ 64))
    (hExec : RustExec N leafSpec c rs rs')       -- from `haxToLowCT_simulates_full`
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
