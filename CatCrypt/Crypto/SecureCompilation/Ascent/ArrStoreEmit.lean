/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ArrStoreLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge

/-!
# The emit keystone for the array-store leaf

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf
(`sgraf812/ascent`).

`Ascent/EmitBridge.lean` welds the scalar value leaf (`SRword`) to emitted jasmin
bytes: `keystone`/`keystone_emit` turn a `Corres SRword …` into
`jcom.denote (…) = ctTransTy val` with `wEnc val` the clean `ZMod 2^64` spec.
`Ascent/ArrStoreLeaf.lean` proves the array analogue on the abstraction side —
`corres_arrStore`, a `Corres SRarr …` value leaf for the dynamic-index write
`RArrStore`, landing in the abstract array-update `arr[idx] := src`
(`memSetDynAbs`) — but had no keystone to weld it to emitted bytes.

This module is that array keystone. It generalises `EmitBridge`'s `SRword` seam to
the `SRarr` array component: the tracked output is the array slot (type
`.memref n`, value `av : Fin n → BitVec 64`), and the abstraction leg's `SRarr`
pins its pointwise encoding `wEnc (av j) = (fa a₀).arr j` to the clean array spec.

## The emit backend does lower `RArrStore`

The array store is *not* an emit wall. `translateDialectControl` (via
`TranslateDialectDirectArms.arrStoreCont`) lowers `RArrStore arr idx src` to the
dialect op `CatCryptDialect.memrefSetDyn n` when the ABI matches — the array slot
resolves to `.memref n`, the index/source to `.sword 64`, and the destination
encodes to `.memref n` (exactly `corres_arrStore`'s `harr`). `cryptoDialectToJasminCom`
then lowers `memrefSetDyn n` to the jasmin `stackStore 64 n` (SIB `STOREIDX`),
with denotational agreement `stackSet_eq_memSetDyn`. So
`rustToJasminCom_endToEnd_topLevel_unconditional` — polymorphic in the output
`CryptoTy` — carries the `.memref n` output the same way it carries `.sword 64`.

## The keystone

`keystone_arr` is the abstract-`Emit` seam: from `Corres SRarr P fa c` run at a
`SRarr`-populated entry `(env₀, a₀)`, the emit-leg output `hEmit`, and the
closed-kernel adapter `hAgree` (the `env₀`-run leaves the array `val` at the slot),
it concludes the emit equation and `∀ j, wEnc (val j) = (fa a₀).arr j` — the
emitted array's pointwise clean spec is the abstract array update.
`keystone_emit_arr` discharges the emit supplier with the real
`rustToJasminCom_endToEnd_topLevel_unconditional` at `t = .memref n`.

`keystone_arrStore` is the non-vacuity witness: `corres_arrStore` discharges the
abstraction-side hypotheses (`Corres`/`SRarr`/`P`/`hAgree`) for the concrete
closed store `RArrStore`, so the array keystone's abstraction inputs are jointly
satisfiable (the bridge is not vacuous); the emit-side data is the standard
covered-kernel input to the end-to-end theorem.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap RustStateInterp encodeTy)
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

/-! ## The array keystone (abstract in the emit map) -/

/-- **`keystone_arr`.** The array analogue of `keystone`. From an ascent
    correspondence `Corres (SRarr n arrName idxName srcName) P fa c` run at a
    `SRarr`-populated entry `(env₀, a₀)`, the emit-leg output `hEmit`
    (`jdenote = Emit val`), and the closed-kernel adapter `hAgree` (the `env₀`-run
    leaves the array `val` at `arrName`), conclude both the emit equation and that
    the emitted array's pointwise clean `ZMod 2^64` spec is `(fa a₀).arr` — the
    abstract array update. `Emit` is abstract; it is instantiated to `ctTransTy`
    in `keystone_emit_arr`. -/
theorem keystone_arr {β : Type} {n : Nat} (Emit : (Fin n → BitVec 64) → β)
    (c : LowCT) (arrName idxName srcName : String) (val : Fin n → BitVec 64)
    (fa : AArr n → AArr n)
    (P : AArr n → Prop)
    (env₀ : SEnvScalar) (a₀ : AArr n) (jdenote : β)
    (hCorres : Corres (SRarr n arrName idxName srcName) P fa c)
    (hSR : SRarr n arrName idxName srcName env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e →
      e arrName = some ⟨.memref n, val⟩)
    (hEmit : jdenote = Emit val) :
    jdenote = Emit val ∧ ∀ j, wEnc (val j) = (fa a₀).arr j := by
  obtain ⟨env', hSem, hSR'⟩ := hCorres env₀ a₀ hSR hP
  obtain ⟨⟨av, hArr, hArrEnc⟩, _, _⟩ := hSR'
  have hcast : (⟨.memref n, av⟩ : (t : CryptoTy) × ⟦t⟧) = ⟨.memref n, val⟩ := by
    have := hArr.symm.trans (hAgree env' hSem)
    exact Option.some.inj this
  obtain rfl : av = val := by simpa using hcast
  exact ⟨hEmit, hArrEnc⟩

/-! ## The composed array keystone (real emit theorem) -/

/-- **`keystone_emit_arr`.** The array keystone with the emit supplier discharged
    by the real end-to-end theorem `rustToJasminCom_endToEnd_topLevel_unconditional`
    at output type `.memref n`: the emitted jasmin program `jcom` denotes to
    `ctTransTy val`, and the emitted array's pointwise clean `ZMod 2^64` spec is the
    abstract array update `(fa a₀).arr`. This is the theorem that makes the
    `corres_arrStore` abstraction result discharge an emit conclusion. The
    `Corres`/`SRarr` entry and the closed-kernel adapter `hAgree` use the
    *satisfiable* route (a populated entry `env₀`, not the empty env the emit leg
    runs at). -/
theorem keystone_emit_arr {n : Nat}
    (c : LowCT) (o : DTransOut ([] : Ctx))
    (N : Nat) (leafSpec : LeafSpec) (rs rs' : RustState)
    (env' : SEnvScalar) (arrName idxName srcName : String)
    (w : CVar o.Γ' (.memref n)) (val : Fin n → BitVec 64)
    (com : Com catCryptDialect ([] : Ctx) (.memref n))
    (jcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.memref n)))
    (fa : AArr n → AArr n)
    (P : AArr n → Prop)
    (env₀ : SEnvScalar) (a₀ : AArr n)
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs')
    (hSem : semScalar c (fun _ => none) = some env')
    (hName : o.vm.lookup arrName = some ⟨.memref n, w⟩)
    (hVal : env' arrName = some ⟨.memref n, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom)
    (hCorres : Corres (SRarr n arrName idxName srcName) P fa c)
    (hSR : SRarr n arrName idxName srcName env₀ a₀) (hP : P a₀)
    (hAgree : ∀ e, semScalar c env₀ = some e →
      e arrName = some ⟨.memref n, val⟩) :
    jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy val
      ∧ ∀ j, wEnc (val j) = (fa a₀).arr j := by
  have hEmit := (rustToJasminCom_endToEnd_topLevel_unconditional
      c o N leafSpec rs rs' env' arrName w val com jcom
      hCov hTrans hExec hSem hName hVal hRet hCom).2
  exact keystone_arr (ctTransTy (t := .memref n)) c arrName idxName srcName val fa P
    env₀ a₀ _ hCorres hSR hP hAgree hEmit

/-! ## Non-vacuity witness for the abstraction/adapter side

For the concrete closed store `RArrStore arr idxVar src`, the `Corres`/`SRarr`/`P`
entry and the closed-kernel adapter `hAgree` are all dischargeable:
`corres_arrStore` supplies `Corres`, an `SRarr`-populated entry env supplies the
state relation, `P = True`, and the store's determinism supplies `hAgree`. This
exhibits that `keystone_arr`'s abstraction-side hypotheses are jointly satisfiable
(the array bridge is not vacuous); the emit-side data is the standard
covered-kernel input to `rustToJasminCom_endToEnd_topLevel_unconditional`. -/
theorem keystone_arrStore {β : Type} {n : Nat} (Emit : (Fin n → BitVec 64) → β)
    (arr src : Located) (idxVar : String)
    (harr : encodeTy arr.locSrc = .memref n)
    (hne_idx : arr.locVar ≠ idxVar) (hne_src : arr.locVar ≠ src.locVar)
    (env₀ : SEnvScalar) (a₀ : AArr n)
    (hSR : SRarr n arr.locVar idxVar src.locVar env₀ a₀)
    (val : Fin n → BitVec 64)
    (hAgree : ∀ e, semScalar (.RArrStore arr idxVar src) env₀ = some e →
      e arr.locVar = some ⟨.memref n, val⟩)
    (jdenote : β) (hEmit : jdenote = Emit val) :
    jdenote = Emit val ∧
      ∀ j, wEnc (val j) = memSetDynAbs a₀.arr a₀.idx a₀.src j :=
  keystone_arr Emit (.RArrStore arr idxVar src) arr.locVar idxVar src.locVar val
    (fun a => { a with arr := memSetDynAbs a.arr a.idx a.src }) (fun _ => True)
    env₀ a₀ jdenote
    (corres_arrStore arr src idxVar harr hne_idx hne_src) hSR trivial hAgree hEmit

end CatCrypt.Crypto.SecureCompilation.Ascent
