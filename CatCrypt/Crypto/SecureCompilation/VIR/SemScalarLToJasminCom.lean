/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardsLeaf
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf

/-!
# Source to jasmin at a pair of leaf oracles

`TranslateDialectScalar.translateDialectControl_denote_ctlWith` relates the dialect
program the front emits for an `IsCoveredSCtl` body, denoted under
`catCryptDenoteWith ls`, to the waist semantics `semScalarL ls`.
`DialectToJasminComLeaf.cryptoDialectToJasminCom_denote_eq_of_transport` relates the
jasmin lowering, denoted under `jasminDenoteWith jls`, to the dialect program at `ls`
whenever `LeafTransport ls jls`. `semScalarLToJasminCom_denote_eq` composes the two:
the lowered program computes the value `semScalarL ls` leaves in a tracked output.

`jleafOfAbs fs` is the jasmin oracle that realises a family of abstract leaves on
`u64` destinations, the counterpart of `Ascent.leafOfAbs fs`, and the two are related
by `LeafTransport` (`leafTransport_leafOfAbs`). At the oracle pair of the worked
kernel `Ascent.leafK`, whose `"arrLoad:0"` and `"select"` leaves take a `TBytes 8`
array, `leafK_semScalarLToJasminCom` is the composed statement with the coverage and
the transport discharged.

## Main definitions

* `jvEnc`, `jhvecSigmaList` — abstraction of jasmin leaf arguments
* `jleafOfAbs` — the jasmin oracle of a family of abstract leaves

## Main results

* `semScalarLToJasminCom_denote_eq` — source `semScalarL ls` to jasmin at
  `jasminDenoteWith jls`, under `LeafTransport ls jls`
* `leafTransport_leafOfAbs` — `leafOfAbs fs` and `jleafOfAbs fs` are related
* `leafK_coveredSCtl`, `leafK_semScalarLToJasminCom` — the instance at `leafK`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SemScalarLToJasminCom

open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- **Source to jasmin at a pair of leaf oracles.** If the dialect front and the jasmin
    lowering both succeed, the entry valuation is consistent with the entry environment,
    and `semScalarL ls` runs `c` to `env'` leaving `val` in the tracked output `name`
    (which the front's post-varmap resolves to the slot `w`), then the lowered program,
    denoted under `jasminDenoteWith jls` for an oracle `jls` related to `ls` by
    `LeafTransport`, computes the transport of `val`. Sublanguage: `IsCoveredSCtl`. -/
theorem semScalarLToJasminCom_denote_eq
    {ls : SemLeafSpec} {jls : JLeafSem} (hT : LeafTransport ls jls)
    {Γ : Ctx} {t : CryptoTy}
    (vm : VarMap Γ) (c : LowCT) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (name : String) (w : CVar o.Γ' t) (val : ⟦t⟧)
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hCov : IsCoveredSCtl c)
    (hTrans : translateDialectControl vm c = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semScalarL ls c env = some env')
    (hName : o.vm.lookup name = some ⟨t, w⟩)
    (hVal : env' name = some ⟨t, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    @Com.denote jasminDialect _ _ (jasminDenoteWith jls) _ _ jcom (ctMapValD V)
      = ctTransTy val := by
  obtain ⟨V', hc', hcont⟩ :=
    translateDialectControl_denote_ctlWith ls hCov vm V env env' o hCons hTrans hSem
  obtain ⟨com', hcom', hden⟩ := hcont (Com.ret (toVIRVar w))
  rw [hRet] at hcom'
  obtain rfl := Option.some.inj hcom'
  rw [cryptoDialectToJasminCom_denote_eq_of_transport hT com V jcom hCom, hden]
  exact congrArg ctTransTy (hc'.lookup_eq hName hVal)

/-! ## The jasmin oracle of a family of abstract leaves -/

/-- The abstraction of a typed jasmin value: `wEnc` of a 64-bit register, `wEnc` of each
    element of a stack array of 64-bit words, and `.other` on every other type. -/
def jvEnc : ((t : JasminTy) × ⟦t⟧) → AVal
  | ⟨.reg 64, w⟩ => .word (wEnc w)
  | ⟨.stackArr 64 n, av⟩ => .arr n (fun j => wEnc (av j))
  | _ => .other

/-- An `HVector` of jasmin values as the list of its typed entries. -/
def jhvecSigmaList : {tys : List JasminTy} → HVector (fun t => ⟦t⟧) tys →
    List ((t : JasminTy) × ⟦t⟧)
  | [], .nil => []
  | t :: _, .cons v rest => ⟨t, v⟩ :: jhvecSigmaList rest

/-- The jasmin oracle realising a family of abstract leaves on 64-bit register
    destinations: at `.reg 64` it returns the word whose `wEnc` encoding is the abstract
    value of the abstracted arguments; at every other type it returns the default. -/
def jleafOfAbs (fs : String → List AVal → ZMod (2 ^ 64)) : JLeafSem :=
  fun name _argTys retTy args =>
    match retTy with
    | .reg 64 => (BitVec.ofNat 64 (fs name ((jhvecSigmaList args).map jvEnc)).val : BitVec 64)
    | t => JasminTy.default t

/-- The abstraction of a transported value is the abstraction of the value. -/
theorem jvEnc_transport : ∀ {t : CryptoTy} (v : ⟦t⟧),
    jvEnc ⟨mapTy t, ctTransTy v⟩ = vEnc ⟨t, v⟩
  | .sword w, v => by
      rcases eq_or_ne w 64 with rfl | hw
      · rfl
      · simp [jvEnc, vEnc, mapTy, ctTransTy, hw]
  | .bit, _ => rfl
  | .unit, _ => rfl
  | .pair _ _, _ => rfl
  | .sum _ _, _ => rfl
  | .memref _, _ => rfl
  | .memrefW w _, _ => by
      rcases eq_or_ne w 64 with rfl | hw
      · rfl
      · simp [jvEnc, vEnc, mapTy, ctTransTy, hw]

/-- The abstractions of a transported argument vector are those of the vector. -/
theorem jhvecSigmaList_ctMapHV : ∀ {tys : List CryptoTy} (args : HVector (fun t => ⟦t⟧) tys),
    (jhvecSigmaList (ctMapHV args)).map jvEnc = (hvecSigmaList args).map vEnc
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      simp only [ctMapHV, jhvecSigmaList, hvecSigmaList, List.map_cons, jvEnc_transport,
        jhvecSigmaList_ctMapHV rest]

/-- `leafOfAbs fs` and `jleafOfAbs fs` are related by `LeafTransport`. -/
theorem leafTransport_leafOfAbs (fs : String → List AVal → ZMod (2 ^ 64)) :
    LeafTransport (leafOfAbs fs) (jleafOfAbs fs) := by
  intro name argTys retTy args hne
  cases retTy with
  | sword w =>
      rcases eq_or_ne w 64 with rfl | hw
      · show (BitVec.ofNat 64 (fs name ((jhvecSigmaList (ctMapHV args)).map jvEnc)).val
            : BitVec 64) = _
        rw [jhvecSigmaList_ctMapHV]
        rfl
      · simp [jleafOfAbs, leafOfAbs, mapTy, hw, ctTransTy, JasminTy.default, CryptoTy.default]
  | bit => rfl
  | unit => rfl
  | pair a b => rfl
  | sum a b => rfl
  | memref n => rfl
  | memrefW w n => exact absurd rfl (hne w n)

/-! ## The worked kernel `leafK` -/

/-- `leafK` is in the control-extended scalar-covered fragment. -/
theorem leafK_coveredSCtl : IsCoveredSCtl leafK :=
  .ofStraight (.rSeq (.rArrLoadLit _ _ _) (.rSelect _ _ _ _))

/-- `semScalarLToJasminCom_denote_eq` at `leafK` and the oracle pair
    `leafOfAbs leafKAbs`, `jleafOfAbs leafKAbs`: whenever the front and the lowering
    succeed on `leafK` from a consistent entry state and `semScalarL` leaves the word
    `val` in `"r"`, the lowered program computes `val`. -/
theorem leafK_semScalarLToJasminCom
    {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (w : CVar o.Γ' (.sword 64)) (val : BitVec 64)
    (com : Com catCryptDialect Γ (.sword 64))
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (hTrans : translateDialectControl vm leafK = some o)
    (hCons : ConsistentS vm V env)
    (hSem : semScalarL (leafOfAbs leafKAbs) leafK env = some env')
    (hName : o.vm.lookup "r" = some ⟨.sword 64, w⟩)
    (hVal : env' "r" = some ⟨.sword 64, val⟩)
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    @Com.denote jasminDialect _ _ (jasminDenoteWith (jleafOfAbs leafKAbs)) _ _ jcom
      (ctMapValD V) = val :=
  semScalarLToJasminCom_denote_eq (leafTransport_leafOfAbs leafKAbs) vm leafK o V env env'
    "r" w val com jcom leafK_coveredSCtl hTrans hCons hSem hName hVal hRet hCom

end CatCrypt.Crypto.SecureCompilation.VIR.SemScalarLToJasminCom
