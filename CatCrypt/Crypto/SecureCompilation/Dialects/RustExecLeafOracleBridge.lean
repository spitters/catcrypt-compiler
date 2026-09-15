/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RustStateSubstrate
public import CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

/-!
# `RustExec` leaf specifications and waist leaf oracles

`RustExec N leafSpec` gives a leaf call its value through the oracle record
`leafSpec : LeafSpec` on tower values (`RustVal t`, byte arrays); `semScalarL ls` gives it
its value through `ls : SemLeafSpec` on encoded values. `cryptoTyOfRustVal` encodes a
tower value at `encodeTy t`, and `encodeRustVal` encodes a typed tower value.

`CallAgrees leafSpec ls` says the `call` oracle, encoded, is `ls` at the leaf name, the
encoded destination type and the encoded arguments, whatever the old destination value
and the argument tower types. `ArrLoadAgrees` is the same statement for the `arrLoad`
oracle at the name `"arrLoad:idx"`. Under these, a `RustExec` step of an `RCall` node
and a `semScalarL ls` step of the same node, from an environment that encodes the
arguments (`TowerEncOn`), bind the destination to encodings of the same value
(`rustExec_semScalarL_call`); likewise for a literal-index read in the leaf case of
`semScalarL` (`rustExec_semScalarL_arrLoadLit`).

The default oracle `defaultLeaf` agrees with `zeroLeafSpec`, whose `call` and `arrLoad`
return the all-zero tower value (`callAgrees_zero`, `arrLoadAgrees_zero`), and at them
the step statements are statements about `semScalar` (`rustExec_semScalar_call_zero`).

The `RSelect` node has no statement here. The `"select"` leaf of `semScalarL` receives
the selector and the two sources; `RustExec` reads the selector from the scalar store
(`rsScalar`), which `TowerEncOn` does not relate to the environment.

## Main definitions

* `encodeRustVal`, `TowerEncOn` — encoding of tower values and of the arguments
* `CallAgrees`, `ArrLoadAgrees` — agreement of a `LeafSpec` with a `SemLeafSpec`
* `zeroLeafSpec` — the leaf specification that agrees with `defaultLeaf`

## Main results

* `rustExec_semScalarL_call`, `rustExec_semScalarL_arrLoadLit` — the step agreements
* `callAgrees_zero`, `arrLoadAgrees_zero`, `rustExec_semScalar_call_zero` — the default
  instances
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecLeafOracleBridge

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

/-- A typed tower value, encoded at `encodeTy` by `cryptoTyOfRustVal`. -/
noncomputable def encodeRustVal (p : (t : TowerType) × RustVal t) : (t : CryptoTy) × ⟦t⟧ :=
  ⟨encodeTy p.1, cryptoTyOfRustVal p.1 p.2⟩

/-- On the names `names`, the environment binds the encoding of the tower heap of `rs`,
    and is unbound where the tower heap is. -/
def TowerEncOn (rs : RustState) (env : SEnvScalar) (names : List String) : Prop :=
  ∀ x ∈ names, env x = (rs.rsTower x).map encodeRustVal

/-- The `call` oracle of `leafSpec`, encoded, is `ls` on the encoded destination type and
    arguments. -/
def CallAgrees (leafSpec : LeafSpec) (ls : SemLeafSpec) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType) (oldV : RustVal dt)
    (args : List ((t : TowerType) × RustVal t)),
    cryptoTyOfRustVal dt (leafSpec.call f dt argTs oldV args)
      = ls f (encodeTy dt) (args.map encodeRustVal)

/-- The `arrLoad` oracle of `leafSpec` at the index `idx`, encoded, is `ls` at the name
    `"arrLoad:idx"` on the encoded destination type and source. -/
def ArrLoadAgrees (leafSpec : LeafSpec) (ls : SemLeafSpec) : Prop :=
  ∀ (dst : Located) (oldV : RustVal dst.locDst) (sv : (t : TowerType) × RustVal t) (idx : Nat),
    cryptoTyOfRustVal dst.locDst (leafSpec.arrLoad dst oldV sv idx)
      = ls ("arrLoad:" ++ toString idx) (encodeTy dst.locDst) [encodeRustVal sv]

/-- The leaf specification whose `call` and `arrLoad` return the all-zero tower value. -/
def zeroLeafSpec : LeafSpec where
  call := fun _ dt _ _ _ => (default : RustVal dt)
  limbStore := fun _ oldV _ _ => oldV
  arrLoad := fun dst _ _ _ => (default : RustVal dst.locDst)

/-- `zeroLeafSpec` agrees with the default oracle on calls. -/
theorem callAgrees_zero : CallAgrees zeroLeafSpec defaultLeaf := by
  intro f dt argTs oldV args
  exact cryptoTyOfRustVal_default dt

/-- `zeroLeafSpec` agrees with the default oracle on array reads. -/
theorem arrLoadAgrees_zero : ArrLoadAgrees zeroLeafSpec defaultLeaf := by
  intro dst oldV sv idx
  exact cryptoTyOfRustVal_default dst.locDst

/-- The argument values of `semScalarL` on an encoding environment are the encodings of
    the argument list `RustExec` passes to the leaf. -/
theorem argVals_towerEnc {rs : RustState} {env : SEnvScalar} :
    ∀ (args : List Located), TowerEncOn rs env (locNames args) →
      argVals env (locNames args)
        = (args.filterMap (fun a => rs.rsTower a.locVar)).map encodeRustVal
  | [], _ => rfl
  | a :: rest, h => by
      have ha := h a.locVar (List.mem_cons_self)
      have ih := argVals_towerEnc rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [argVals, locNames, List.map_cons, List.filterMap_cons] at ih ⊢
      rw [ha]
      cases hr : rs.rsTower a.locVar with
      | none => simpa using ih
      | some p => simpa using ih

theorem locatedLookup_locatedUpdate (rs : RustState) (loc : Located) (v : RustVal loc.locDst) :
    locatedLookup (locatedUpdate rs loc v) loc = some v := by
  simp [locatedLookup, locatedUpdate, rsSetTower_same]

/-- **The call step.** A `RustExec` step of `RCall f dest args` writes a value `v` to
    `dest`, and `semScalarL ls` binds `dest` to its encoding, when the leaf specification
    agrees with `ls` and the environment encodes the arguments. -/
theorem rustExec_semScalarL_call {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} {dest : Located} {args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCall f dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args)) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      semScalarL ls (.RCall f dest args) env =
        some (env.upd dest.locVar (t := encodeTy dest.locDst)
          (cryptoTyOfRustVal dest.locDst v)) := by
  cases hexec with
  | call _ _ _ _ oldDestV argList _ hargs _ =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rCall, hagree, hargs, argVals_towerEnc args henc]

/-- **The literal-index read step, leaf case.** When the read is not a word read of a
    `TArr _ .TU64` array bound as a `.memref`, a `RustExec` step writes a value `v` to
    `dst`, and `semScalarL ls` binds `dst` to its encoding, when the `arrLoad` oracle
    agrees with `ls` and the environment encodes the source. -/
theorem rustExec_semScalarL_arrLoadLit {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : ArrLoadAgrees leafSpec ls) {dst src : Located} {idx : Nat}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RArrLoadLit dst src idx) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env [src.locVar])
    (hleaf : ∀ (k n : Nat) (arr : Fin n → BitVec 64), dst.locSrc = .TU64 →
      src.locSrc = .TArr k .TU64 → env src.locVar = some ⟨.memref n, arr⟩ → False) :
    ∃ v : RustVal dst.locDst, locatedLookup rs' dst = some v ∧
      semScalarL ls (.RArrLoadLit dst src idx) env =
        some (env.upd dst.locVar (t := encodeTy dst.locDst)
          (cryptoTyOfRustVal dst.locDst v)) := by
  cases hexec with
  | arrLoadLit _ _ _ _ oldV srcV _ hsrc =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rArrLoadLit_leaf ls dst src idx env hleaf, hagree]
      have hs := henc src.locVar (List.mem_singleton_self _)
      have hv : rs.rsTower src.locVar = some ⟨src.locDst, srcV⟩ := by
        simp only [locatedLookup] at hsrc
        split at hsrc
        · rename_i t v' hrt
          split at hsrc
          · rename_i h
            subst h
            cases hsrc
            exact hrt
          · cases hsrc
        · cases hsrc
      have hargs : argVals env (locNames [src]) = [encodeRustVal ⟨src.locDst, srcV⟩] := by
        simp [argVals, locNames, hs, hv]
      rw [hargs]

/-- At `zeroLeafSpec` and the default oracle, the call step is a statement about
    `semScalar`. -/
theorem rustExec_semScalar_call_zero {N : Nat} {f : String} {dest : Located}
    {args : List Located} {rs rs' : RustState}
    (hexec : RustExec N zeroLeafSpec (.RCall f dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args)) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      semScalar (.RCall f dest args) env =
        some (env.upd dest.locVar (t := encodeTy dest.locDst)
          (cryptoTyOfRustVal dest.locDst v)) := by
  obtain ⟨v, hv, hs⟩ := rustExec_semScalarL_call callAgrees_zero hexec henc
  exact ⟨v, hv, (semScalarL_default _ env).symm.trans hs⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecLeafOracleBridge
