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

The default oracle `defaultLeaf` agrees with `zeroLeafSpec`, whose `call`, `tupleLoad`,
`arrStore` and `arrLoad` return the all-zero tower value (`callAgrees_zero`,
`tupleLoadLeafAgrees_zero`, `arrStoreAgrees_zero`, `arrLoadAgrees_zero`), and at them the
step statements are statements about `semScalar` (`rustExec_semScalar_call_zero`).

`TupleLoadLeafAgrees` and `ArrStoreAgrees` are the same statements for the `tupleLoad`
oracle at `"tupleLoad:idx"` and the `arrStore` oracle at `"arrStore:idx"`, the latter
receiving the old array and the source. Under them, and `CallAgrees`, the steps of
`RCallDstThreaded`, `RTupleLoad`, the leaf case of `RArrStoreLit`, `RCallSwap` and
`RCallN` bind their destinations to encodings of the values `RustExec` writes
(`rustExec_semScalarL_callDstThreaded`, `rustExec_semScalarL_tupleLoad`,
`rustExec_semScalarL_arrStoreLit`, `rustExec_semScalarL_callSwap`,
`rustExec_semScalarL_callN`); the two-destination and multi-destination forms require the
destinations written before an argument is read to be outside the arguments, since
`RustExec` reads the arguments once and `semScalarL` before each write. `RustExec` copies
the old destination of `RCloneCall` into the clone variable, and `semScalarL` binds it to
the `"clone"` leaf; `CloneAgrees ls` says that leaf returns its argument, and under it the
clone step agrees (`rustExec_semScalarL_cloneCall`).

The `RSelect` node has no statement here. The `"select"` leaf of `semScalarL` receives
the selector and the two sources; `RustExec` reads the selector from the scalar store
(`rsScalar`), which `TowerEncOn` does not relate to the environment.

## Main definitions

* `encodeRustVal`, `TowerEncOn` — encoding of tower values and of the arguments
* `CallAgrees`, `ArrLoadAgrees`, `TupleLoadLeafAgrees`, `ArrStoreAgrees`, `CloneAgrees` —
  agreement of a `LeafSpec`, and of the `"clone"` leaf, with a `SemLeafSpec`
* `zeroLeafSpec` — the leaf specification that agrees with `defaultLeaf`

## Main results

* `rustExec_semScalarL_call`, `rustExec_semScalarL_arrLoadLit`,
  `rustExec_semScalarL_callDstThreaded`, `rustExec_semScalarL_tupleLoad`,
  `rustExec_semScalarL_arrStoreLit`, `rustExec_semScalarL_callSwap`,
  `rustExec_semScalarL_cloneCall`, `rustExec_semScalarL_callN` — the step agreements
* `callAgrees_zero`, `arrLoadAgrees_zero`, `tupleLoadLeafAgrees_zero`,
  `arrStoreAgrees_zero`, `rustExec_semScalar_call_zero` — the default instances
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

/-- The `tupleLoad` oracle of `leafSpec` at the index `idx`, encoded, is `ls` at the name
    `"tupleLoad:idx"` on the encoded destination type and source. -/
def TupleLoadLeafAgrees (leafSpec : LeafSpec) (ls : SemLeafSpec) : Prop :=
  ∀ (dst : Located) (oldV : RustVal dst.locDst) (sv : (t : TowerType) × RustVal t) (idx : Nat),
    cryptoTyOfRustVal dst.locDst (leafSpec.tupleLoad dst oldV sv idx)
      = ls ("tupleLoad:" ++ toString idx) (encodeTy dst.locDst) [encodeRustVal sv]

/-- The `arrStore` oracle of `leafSpec` at the index `idx`, encoded, is `ls` at the name
    `"arrStore:idx"` on the encoded array type, the encoded old array and the encoded
    source. -/
def ArrStoreAgrees (leafSpec : LeafSpec) (ls : SemLeafSpec) : Prop :=
  ∀ (arr : Located) (oldV : RustVal arr.locDst) (sv : (t : TowerType) × RustVal t) (idx : Nat),
    cryptoTyOfRustVal arr.locDst (leafSpec.arrStore arr oldV idx sv)
      = ls ("arrStore:" ++ toString idx) (encodeTy arr.locDst)
          [encodeRustVal ⟨arr.locDst, oldV⟩, encodeRustVal sv]

/-- The `"clone"` leaf of `ls` returns its one argument, at every type. -/
def CloneAgrees (ls : SemLeafSpec) : Prop :=
  ∀ (t : CryptoTy) (v : ⟦t⟧), ls "clone" t [⟨t, v⟩] = v

/-- The leaf specification whose `call`, `tupleLoad`, `arrStore` and `arrLoad` return the
    all-zero tower value. -/
def zeroLeafSpec : LeafSpec where
  call := fun _ dt _ _ _ => (default : RustVal dt)
  limbStore := fun _ oldV _ _ => oldV
  tupleLoad := fun dst _ _ _ => (default : RustVal dst.locDst)
  arrStore := fun arr _ _ _ => (default : RustVal arr.locDst)
  arrLoad := fun dst _ _ _ => (default : RustVal dst.locDst)

/-- `zeroLeafSpec` agrees with the default oracle on calls. -/
theorem callAgrees_zero : CallAgrees zeroLeafSpec defaultLeaf := by
  intro f dt argTs oldV args
  exact cryptoTyOfRustVal_default dt

/-- `zeroLeafSpec` agrees with the default oracle on array reads. -/
theorem arrLoadAgrees_zero : ArrLoadAgrees zeroLeafSpec defaultLeaf := by
  intro dst oldV sv idx
  exact cryptoTyOfRustVal_default dst.locDst

/-- `zeroLeafSpec` agrees with the default oracle on tuple component reads. -/
theorem tupleLoadLeafAgrees_zero : TupleLoadLeafAgrees zeroLeafSpec defaultLeaf := by
  intro dst oldV sv idx
  exact cryptoTyOfRustVal_default dst.locDst

/-- `zeroLeafSpec` agrees with the default oracle on array writes. -/
theorem arrStoreAgrees_zero : ArrStoreAgrees zeroLeafSpec defaultLeaf := by
  intro arr oldV sv idx
  exact cryptoTyOfRustVal_default arr.locDst

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

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (inlineArithRecipe) in
/-- **The call step.** A `RustExec` step of `RCall f dest args` on a name outside
    `inlineArithTable` writes a value `v` to `dest`, and `semScalarL ls` binds `dest` to
    its encoding, when the leaf specification agrees with `ls` and the environment encodes
    the arguments. -/
theorem rustExec_semScalarL_call {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} (hni : inlineArithRecipe f = none)
    {dest : Located} {args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCall f dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args)) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      semScalarL ls (.RCall f dest args) env =
        some (env.upd dest.locVar (t := encodeTy dest.locDst)
          (cryptoTyOfRustVal dest.locDst v)) := by
  cases hexec with
  | call _ _ _ _ oldDestV argList _ hargs _ =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rCall_of_recipe_none ls hni, hagree, hargs, argVals_towerEnc args henc]

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

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (inlineArithRecipe) in
/-- At `zeroLeafSpec` and the default oracle, the call step on a name outside
    `inlineArithTable` is a statement about `semScalar`. -/
theorem rustExec_semScalar_call_zero {N : Nat} {f : String} (hni : inlineArithRecipe f = none)
    {dest : Located} {args : List Located} {rs rs' : RustState}
    (hexec : RustExec N zeroLeafSpec (.RCall f dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args)) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      semScalar (.RCall f dest args) env =
        some (env.upd dest.locVar (t := encodeTy dest.locDst)
          (cryptoTyOfRustVal dest.locDst v)) := by
  obtain ⟨v, hv, hs⟩ := rustExec_semScalarL_call callAgrees_zero hni hexec henc
  exact ⟨v, hv, (semScalarL_default _ env).symm.trans hs⟩

/-! ## The multi-destination, threaded, tuple and array-writing leaves -/

/-- A located lookup is the tower binding at the located type. -/
theorem rsTower_of_locatedLookup {rs : RustState} {loc : Located} {v : RustVal loc.locDst}
    (h : locatedLookup rs loc = some v) : rs.rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  simp only [locatedLookup] at h
  split at h
  · rename_i t v' hrt
    split at h
    · rename_i ht
      subst ht
      cases h
      exact hrt
    · cases h
  · cases h

/-- Located lookups agree on states whose tower heaps agree at the name. -/
theorem locatedLookup_congr {rs rs' : RustState} (loc : Located)
    (h : rs'.rsTower loc.locVar = rs.rsTower loc.locVar) :
    locatedLookup rs' loc = locatedLookup rs loc := by
  unfold locatedLookup; rw [h]

/-- The value a `RustExec` step of `RCall f dest args` writes, as the oracle `ls` at `f` on
    the argument values of an encoding environment, with the frame outside `dest`. -/
theorem rustExec_call_value {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} {dest : Located} {args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCall f dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args)) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      ls f (encodeTy dest.locSrc) (argVals env (locNames args)) = cryptoTyOfRustVal dest.locDst v ∧
      ∀ y, y ≠ dest.locVar → rs'.rsTower y = rs.rsTower y := by
  cases hexec with
  | call _ _ _ _ oldDestV argList _ hargs _ =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_, fun y hy => ?_⟩
      · rw [hagree, hargs, argVals_towerEnc args henc]
      · exact rsSetTower_other _ _ _ _ (Ne.symm hy)

/-- **The destination-threaded call step.** A `RustExec` step of
    `RCallDstThreaded f dst args` writes a value `v` to `dst`, and `semScalarL ls` binds
    `dst` to its encoding, when the leaf specification agrees with `ls` and the
    environment encodes the destination and the arguments. -/
theorem rustExec_semScalarL_callDstThreaded {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} {dst : Located} {args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCallDstThreaded f dst args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames (dst :: args))) :
    ∃ v : RustVal dst.locDst, locatedLookup rs' dst = some v ∧
      semScalarL ls (.RCallDstThreaded f dst args) env =
        some (env.upd dst.locVar (t := encodeTy dst.locDst)
          (cryptoTyOfRustVal dst.locDst v)) := by
  cases hexec with
  | callDstThreaded _ _ _ _ oldDestV argList _ hargs _ =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rCallDstThreaded, hagree, hargs, argVals_towerEnc (dst :: args) henc]

/-- **The tuple component read step.** A `RustExec` step of `RTupleLoad dst src idx`
    writes a value `v` to `dst`, and `semScalarL ls` binds `dst` to its encoding, when the
    `tupleLoad` oracle agrees with `ls` and the environment encodes the source. -/
theorem rustExec_semScalarL_tupleLoad {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : TupleLoadLeafAgrees leafSpec ls) {dst src : Located} {idx : Nat}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RTupleLoad dst src idx) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env [src.locVar]) :
    ∃ v : RustVal dst.locDst, locatedLookup rs' dst = some v ∧
      semScalarL ls (.RTupleLoad dst src idx) env =
        some (env.upd dst.locVar (t := encodeTy dst.locDst)
          (cryptoTyOfRustVal dst.locDst v)) := by
  cases hexec with
  | tupleLoad _ _ _ _ oldV srcV _ hsrc =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rTupleLoad, hagree]
      have hargs : argVals env (locNames [src]) = [encodeRustVal ⟨src.locDst, srcV⟩] := by
        simp [argVals, locNames, henc src.locVar (List.mem_singleton_self _),
          rsTower_of_locatedLookup hsrc]
      rw [hargs]

/-- **The literal-index write step, leaf case.** When the write is not a word write to a
    `TArr _ .TU64` array bound as a `.memref`, a `RustExec` step of
    `RArrStoreLit arr idx src` writes a value `v` to `arr`, and `semScalarL ls` binds `arr`
    to its encoding, when the `arrStore` oracle agrees with `ls` and the environment
    encodes the array and the source. -/
theorem rustExec_semScalarL_arrStoreLit {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : ArrStoreAgrees leafSpec ls) {arr src : Located} {idx : Nat}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RArrStoreLit arr idx src) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames [arr, src]))
    (hleaf : ∀ (k n : Nat) (a : Fin n → BitVec 64) (v : BitVec 64), arr.locSrc = .TArr k .TU64 →
      env arr.locVar = some ⟨.memref n, a⟩ → env src.locVar = some ⟨.sword 64, v⟩ → False) :
    ∃ v : RustVal arr.locDst, locatedLookup rs' arr = some v ∧
      semScalarL ls (.RArrStoreLit arr idx src) env =
        some (env.upd arr.locVar (t := encodeTy arr.locDst)
          (cryptoTyOfRustVal arr.locDst v)) := by
  cases hexec with
  | arrStoreLit _ _ _ _ oldV srcV harr hsrc =>
      refine ⟨_, locatedLookup_locatedUpdate _ _ _, ?_⟩
      rw [semScalarL_rArrStoreLit_leaf ls arr src idx env hleaf, hagree]
      have hargs : argVals env (locNames [arr, src]) =
          [encodeRustVal ⟨arr.locDst, oldV⟩, encodeRustVal ⟨src.locDst, srcV⟩] := by
        simp [argVals, locNames, henc arr.locVar (by simp [locNames]),
          henc src.locVar (by simp [locNames]), rsTower_of_locatedLookup harr,
          rsTower_of_locatedLookup hsrc]
      rw [hargs]

/-- **The two-destination call step.** A `RustExec` step of `RCallSwap f dest1 dest2 args`,
    with `dest1` outside the arguments and distinct from `dest2`, writes `v1` to `dest1`
    and `v2` to `dest2`, and `semScalarL ls` binds them to their encodings in that order,
    when the leaf specification agrees with `ls` and the environment encodes the
    arguments. -/
theorem rustExec_semScalarL_callSwap {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} {dest1 dest2 : Located} {args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args))
    (hd1 : dest1.locVar ∉ locNames args) (hne : dest1.locVar ≠ dest2.locVar) :
    ∃ (v1 : RustVal dest1.locDst) (v2 : RustVal dest2.locDst),
      locatedLookup rs' dest1 = some v1 ∧ locatedLookup rs' dest2 = some v2 ∧
      semScalarL ls (.RCallSwap f dest1 dest2 args) env =
        some ((env.upd dest1.locVar (t := encodeTy dest1.locDst)
            (cryptoTyOfRustVal dest1.locDst v1)).upd dest2.locVar (t := encodeTy dest2.locDst)
          (cryptoTyOfRustVal dest2.locDst v2)) := by
  cases hexec with
  | callSwap _ _ _ _ _ rs1 _ h1 h2 =>
      obtain ⟨v1, hv1, hX, hfr1⟩ := rustExec_call_value hagree h1 henc
      have henc1 : TowerEncOn rs1
          (env.upd dest1.locVar (t := encodeTy dest1.locSrc) (cryptoTyOfRustVal dest1.locDst v1))
          (locNames args) := by
        intro x hx
        have hxd : x ≠ dest1.locVar := fun h => hd1 (h ▸ hx)
        rw [hfr1 x hxd, ← henc x hx]
        simp [SEnvScalar.upd, hxd]
      obtain ⟨v2, hv2, hY, hfr2⟩ := rustExec_call_value hagree h2 henc1
      refine ⟨v1, v2, ?_, hv2, ?_⟩
      · rw [locatedLookup_congr dest1 (hfr2 _ hne)]; exact hv1
      · rw [semScalarL_rCallSwap, hX, hY]

/-- **The clone-and-call step.** A `RustExec` step of
    `RCloneCall cv cloneTy oldDest innerF dest args` from a state binding `oldDest` to
    `p` copies `p` to `cv` and writes a value `v` to `dest`; `semScalarL ls` binds `cv` to
    the encoding of `p` and `dest` to the encoding of `v`, when the leaf specification
    agrees with `ls`, the `"clone"` leaf of `ls` returns its argument, and the environment
    encodes the old destination and the arguments. -/
theorem rustExec_semScalarL_cloneCall {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) (hclone : CloneAgrees ls) {cv : String}
    {cloneTy : TowerType} {oldDest : Located} {innerF : String} {dest : Located}
    {args : List Located} {rs rs' : RustState}
    (hexec : RustExec N leafSpec (.RCloneCall cv cloneTy oldDest innerF dest args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args))
    (hold : TowerEncOn rs env [oldDest.locVar]) (p : (t : TowerType) × RustVal t)
    (hp : rs.rsTower oldDest.locVar = some p) :
    ∃ v : RustVal dest.locDst, locatedLookup rs' dest = some v ∧
      semScalarL ls (.RCloneCall cv cloneTy oldDest innerF dest args) env =
        some ((env.upd cv (t := encodeTy p.1) (cryptoTyOfRustVal p.1 p.2)).upd dest.locVar
          (t := encodeTy dest.locDst) (cryptoTyOfRustVal dest.locDst v)) := by
  cases hexec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hrs h1 =>
      have hoe : env oldDest.locVar = some ⟨encodeTy p.1, cryptoTyOfRustVal p.1 p.2⟩ := by
        rw [hold oldDest.locVar (List.mem_singleton_self _), hp]; rfl
      have hcl : argVals env [oldDest.locVar] = [⟨encodeTy p.1, cryptoTyOfRustVal p.1 p.2⟩] := by
        simp [argVals, hoe]
      subst hrs
      rw [hp] at h1
      have henc1 : TowerEncOn (rsSetTower rs cv (Option.getD (some p) ⟨cloneTy, default⟩))
          (env.upd cv (t := encodeTy p.1) (cryptoTyOfRustVal p.1 p.2)) (locNames args) := by
        intro x hx
        by_cases hxc : x = cv
        · subst hxc
          simp [SEnvScalar.upd, rsSetTower_same, encodeRustVal]
        · rw [rsSetTower_other _ _ _ _ (Ne.symm hxc), ← henc x hx]
          simp [SEnvScalar.upd, hxc]
      obtain ⟨v, hv, hY, _⟩ := rustExec_call_value hagree h1 henc1
      refine ⟨v, hv, ?_⟩
      rw [semScalarL_rCloneCall ls cv cloneTy oldDest innerF dest args env _ _ hoe, hcl,
        hclone, hY]

/-- The destination fold of `RCallN` and the `RustExec` fold agree on the destinations,
    when the leaf specification agrees with `ls`, the argument values encode the argument
    list read once, and no destination is an argument. -/
theorem callN_towerEnc {leafSpec : LeafSpec} {ls : SemLeafSpec} (hagree : CallAgrees leafSpec ls)
    (f : String) (args : List Located) (argTs : List TowerType)
    (argList : List ((t : TowerType) × RustVal t)) :
    ∀ (dests : List Located) (i : Nat) (rs : RustState) (env : SEnvScalar),
      argVals env (locNames args) = argList.map encodeRustVal →
      (∀ d ∈ dests, d.locVar ∉ locNames args) →
      TowerEncOn (callNUpdate leafSpec f argTs argList i dests rs)
        (semCallNDestsL ls f args dests i env) (locNames dests)
  | [], _, _, _, _, _ => fun x hx => absurd hx (by simp [locNames])
  | d :: rest, i, rs, env, hargs, hdisj => by
      intro x hx
      have hd : d.locVar ∉ locNames args := hdisj d List.mem_cons_self
      have ih := callN_towerEnc hagree f args argTs argList rest (i + 1)
        (locatedUpdate rs d (leafSpec.call (callNLeafName f i) d.locDst argTs
          ((locatedLookup rs d).getD default) argList))
        (env.upd d.locVar (t := encodeTy d.locDst)
          (ls (callNLeafName f i) (encodeTy d.locDst) (argVals env (locNames args))))
        ((argVals_upd_other env d.locVar
          (ls (callNLeafName f i) (encodeTy d.locDst) (argVals env (locNames args)))
          (locNames args) hd).trans hargs)
        (fun d' hd' => hdisj d' (List.mem_cons_of_mem _ hd'))
      by_cases hxr : x ∈ locNames rest
      · exact ih x hxr
      · have hxd : x = d.locVar := by
          simp only [locNames, List.map_cons, List.mem_cons] at hx
          rcases hx with h | h
          · exact h
          · exact absurd h hxr
        subst hxd
        show semCallNDestsL ls f args rest (i + 1) _ d.locVar =
          ((callNUpdate leafSpec f argTs argList (i + 1) rest _).rsTower d.locVar).map
            encodeRustVal
        rw [semCallNDestsL_other ls f args rest (i + 1) _ _ hxr,
          rsTower_callNUpdate_other leafSpec f argTs argList rest (i + 1) _ _ hxr,
          locatedUpdate_dest]
        simp only [SEnvScalar.upd, ite_true, Option.map_some, encodeRustVal]
        rw [hagree, hargs]

/-- **The multi-destination call step.** After a `RustExec` step of `RCallN f dests args`
    with no destination among the arguments, the `semScalarL ls` fold binds each
    destination to the encoding of the value written, when the leaf specification agrees
    with `ls` and the environment encodes the arguments. -/
theorem rustExec_semScalarL_callN {N : Nat} {leafSpec : LeafSpec} {ls : SemLeafSpec}
    (hagree : CallAgrees leafSpec ls) {f : String} {dests args : List Located}
    {rs rs' : RustState} (hexec : RustExec N leafSpec (.RCallN f dests args) rs rs')
    {env : SEnvScalar} (henc : TowerEncOn rs env (locNames args))
    (hdisj : ∀ d ∈ dests, d.locVar ∉ locNames args) :
    TowerEncOn rs' (semCallNDestsL ls f args dests 0 env) (locNames dests) ∧
      semScalarL ls (.RCallN f dests args) env = some (semCallNDestsL ls f args dests 0 env) := by
  cases hexec with
  | callN _ _ _ _ argList hargs _ _ =>
      exact ⟨callN_towerEnc hagree f args _ argList dests 0 rs env
        (by rw [hargs]; exact argVals_towerEnc args henc) hdisj, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecLeafOracleBridge
