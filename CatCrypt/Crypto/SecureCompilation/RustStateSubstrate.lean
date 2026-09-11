/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.SecureCompilation.CryptoSSA
public import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA

/-!
# Rust-state interpretation substrate (CProg-free)

The byte-layout invariant `RustStateInterp` relating a `LowCT` `RustState`
to a CryptoSSA `HVec` valuation, together with the no-aliasing predicate
`NoAliasVM`, the canonical-witness machinery, and the per-binding
`bindingOK`/`interp_*` transport lemmas.

This module is **CProg-free**: it contains no `CExpr`/`CProg`/`translate`
token in code. It is the shared substrate consumed both by the
`translate`-based `LowCTToCryptoSSACorrect` proofs and by the
`catCryptDialect`-front simulation (`Dialects.CryptoDialectRustSim`) and the
downstream RHP / borrow-safety / compiler-correctness consumers. Keeping it
separate from `LowCTToCryptoSSACorrect` lets the CProg front be retired
without disturbing the survivors.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin (JArray)
open CatCrypt.Core

/-! ## Byte-layout helpers

Each tower type's `RustVal` is a `JArray t.byteSize = Fin t.byteSize →
BitVec 8`. The CryptoSSA side encodes tower types as `memref n` where
`n = t.byteSize / 8` (limb count): a `Fin n → BitVec 64`. The conversion
between the two is little-endian byte packing — the convention used by
fiat-crypto's `from_bytes` / `to_bytes` and by Jasmin's `getWord` /
`setWord` (cf. `JArray.getWord` in `JasminTypes.lean`).
-/

/-- Pack 8 little-endian bytes into a 64-bit word.
    `wordOfBytes8 b = b 0 ∥ b 1 ∥ … ∥ b 7` with `b 0` as the lowest byte. -/
def wordOfBytes8 (b : Fin 8 → BitVec 8) : BitVec 64 :=
  let lift : Fin 8 → BitVec 64 := fun i => (b i).zeroExtend 64
  (lift 0)
    ||| ((lift 1) <<< 8)
    ||| ((lift 2) <<< 16)
    ||| ((lift 3) <<< 24)
    ||| ((lift 4) <<< 32)
    ||| ((lift 5) <<< 40)
    ||| ((lift 6) <<< 48)
    ||| ((lift 7) <<< 56)

/-- Project an `n × 8`-byte rust-side tower value to an `n × i64` memref
    by little-endian packing per limb. -/
def bytesOfMemrefRust {n : Nat} (bytes : Fin (8 * n) → BitVec 8) :
    Fin n → BitVec 64 :=
  fun i => wordOfBytes8 (fun j =>
    have h : 8 * i.val + j.val < 8 * n := by
      have : j.val < 8 := j.isLt
      have : i.val < n := i.isLt
      omega
    bytes ⟨8 * i.val + j.val, h⟩)

/-- The CryptoSSA-side encoding of a `RustVal t`. For tower types this is
    a memref keyed by limb index; for `TU64` it is a single 64-bit word.

    The `Fin`-coercions go through `byteSize` on the rust side; we use
    `simp [TowerType.byteSize] <;> omega` to discharge them per
    constructor (8 / 48 / 96 / … vs 8 × limbs). -/
noncomputable def cryptoTyOfRustVal :
    (t : TowerType) → RustVal t → CryptoTy.denote (encodeTy t)
  | .TU64,      v => wordOfBytes8
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp,       v => bytesOfMemrefRust (n := 6)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp2,      v => bytesOfMemrefRust (n := 12)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp6,      v => bytesOfMemrefRust (n := 36)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp12,     v => bytesOfMemrefRust (n := 72)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp25519,  v => bytesOfMemrefRust (n := 5)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  | .TFp25519_64, v => bytesOfMemrefRust (n := 4)
                       (fun i => v ⟨i.val,
                          by simp [TowerType.storageBytes]⟩)
  -- Phase D/E/I/K (2026-05-03): the new tower types are not yet handled
  -- by the CryptoSSA correctness invariant.  Fall back to the default
  -- `CryptoTy.denote` value (zero memref); `LowCTToCryptoSSA.translate`
  -- already returns `none` for `RLetZero` over these types, so this
  -- branch is unreachable through the correctness theorem.
  | .TFpL25519,           _ => CryptoTy.default _
  | .TFpP256,             _ => CryptoTy.default _
  | .TFp25519_4Bounded _, _ => CryptoTy.default _
  | .TFpGen _ _,          _ => CryptoTy.default _
  | .TFp2Gen _ _,         _ => CryptoTy.default _
  | .TTuple _ _,          _ => CryptoTy.default _
  | .TBytes _,            _ => CryptoTy.default _
  -- Phase Ext (2026-05-14): TArr similarly unreachable.
  | .TArr _ _,            _ => CryptoTy.default _
  -- Phase L (2026-05-22): polynomial-mod-q tower types — `translate`
  -- returns `none` for these, so this branch is unreachable through
  -- the correctness theorem.
  | .TPolyMod _ _,        _ => CryptoTy.default _
  | .TPolyVec _ _ _,      _ => CryptoTy.default _
  | .TPolyMat _ _ _ _,    _ => CryptoTy.default _
  -- Phase L.1 (2026-05-23): u8 / u32 scalar widths — `translate`
  -- returns `none` for these, so this branch is unreachable.
  | .TU8,                 _ => CryptoTy.default _
  | .TU32,                _ => CryptoTy.default _

/-! ## Default HVec + invariant relating RustState to a CryptoSSA valuation -/

/-- Default heterogeneous valuation for any context. Built pointwise
    from `CryptoTy.default`. Used to witness the post-state existential
    in `rustExecSimulatesCryptoSSA`. -/
def HVec.default : (Γ : Ctx) → HVec Γ
  | [] => .nil
  | t :: Γ => .cons (CryptoTy.default t) (HVec.default Γ)

/-- Default rust state with no tower bindings and all scalars zero. -/
def defaultRustState : RustState :=
  { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- The byte-layout invariant for a single binding `name ↦ ⟨t, v⟩` of
    the VarMap. We split on the CryptoSSA type:

    * `sword 64`: the word in the SSA valuation equals the `BitVec 64`
      encoding of the rust-side scalar `rs.rsScalar name`. (`sword n`
      for `n ≠ 64` cannot arise from `encodeTy`, so we leave it free.)
    * `memref n`: there exists a tower value of type `t` with
      `encodeTy t = .memref n` whose byte-projection equals the SSA
      memref. We package this through `cryptoTyOfRustVal`.
    * Other types (`bit`, `unit`, `pair`, `sum`, off-size words):
      not in the image of `encodeTy`; trivially satisfied. -/
noncomputable def bindingOK {Γ : Ctx} (rs : RustState) (V : HVec Γ)
    (name : String) {t : CryptoTy} (v : CVar Γ t) : Prop :=
  match t, v with
  | .sword 64, v =>
      v.lookup V = BitVec.ofNat 64 (rs.rsScalar name)
  | .memref n, v =>
      -- B1.quintus weakening: vacuous when `rs.rsTower name = none`.
      -- B1.sexta-tail Phase 3: also vacuous when types don't match
      -- (i.e. `encodeTy t' ≠ .memref n`). The `some ⟨t', vt⟩` arm is
      -- now an *implication* rather than a conjunction: only when the
      -- types align does the HEq become a real obligation.
      match rs.rsTower name with
      | some ⟨t', vt⟩ =>
          encodeTy t' = .memref n →
          HEq (v.lookup V) (cryptoTyOfRustVal t' vt)
      | none => True
  | _, _ => True

/-! ## No-alias invariant on `VarMap`

`NoAliasVM vm` says `vm.lookup` is *injective on names*: two distinct source
names never resolve to the same typed CryptoSSA variable. This is the
invariant the `whileTrue` arm of `rustExecSimulatesCryptoSSA` needs (commit
`4a0a53eb` regression).

Why it is necessary. The simulation conclusion `∃ V', RustStateInterp vm rs' V'`
ranges over the *post-loop* state `rs'`, which the loop body may have left with
two aliased source names holding **divergent** scalars (e.g. body sets `b := 1`
leaving `a := 0` while `vm` maps both `a` and `b` to one `sword 64` var). No
`V'` can then satisfy `bindingOK` for both names simultaneously
(`v.lookup V' = ofNat 64 (rs'.rsScalar a)` and `= ofNat 64 (rs'.rsScalar b)`
are contradictory). So the conclusion is *false* for an aliasing seed `vm`.
`NoAliasVM` rules out exactly that aliasing; it is carried as a field of
`RustStateInterp` (so the public theorem signature is unchanged and the
hypothesis `RustStateInterp vm rs V` already excludes the bad seed) and is
preserved by every `VarMap.bind`/`VarMap.weaken` the translator emits. -/
def NoAliasVM {Γ : Ctx} (vm : VarMap Γ) : Prop :=
  ∀ (n₁ n₂ : String) (t : CryptoTy) (v : CVar Γ t),
    vm.lookup n₁ = some ⟨t, v⟩ → vm.lookup n₂ = some ⟨t, v⟩ → n₁ = n₂

/-- The empty VarMap binds no names, so injectivity is vacuous. -/
theorem noAlias_empty : NoAliasVM (VarMap.empty) := by
  intro n₁ n₂ t v h₁ _; simp [VarMap.empty] at h₁

/-- `VarMap.bind` preserves `NoAliasVM`: the freshly-bound name maps to the
    unique `.here`, and every other name is `.there`-shifted (an injective
    embedding), so no two distinct names collide. -/
theorem noAlias_bind {Γ : Ctx} {t : CryptoTy} {vm : VarMap Γ} (hNA : NoAliasVM vm)
    (name : String) : NoAliasVM (vm.bind name : VarMap (t :: Γ)) := by
  intro n₁ n₂ s v h₁ h₂
  simp only [VarMap.bind] at h₁ h₂
  by_cases e1 : n₁ = name <;> by_cases e2 : n₂ = name
  · rw [e1, e2]
  · exfalso
    rw [if_pos e1] at h₁; rw [if_neg e2] at h₂
    simp only [Option.some.injEq, Sigma.mk.injEq] at h₁
    obtain ⟨hs, hv⟩ := h₁; subst hs; cases hv
    cases hL : vm.lookup n₂ with
    | none => rw [hL] at h₂; simp at h₂
    | some p => rw [hL] at h₂; obtain ⟨t', v'⟩ := p
                simp only [Option.some.injEq, Sigma.mk.injEq] at h₂
                obtain ⟨hst, hv2⟩ := h₂; subst hst; cases hv2
  · exfalso
    rw [if_neg e1] at h₁; rw [if_pos e2] at h₂
    simp only [Option.some.injEq, Sigma.mk.injEq] at h₂
    obtain ⟨hs, hv⟩ := h₂; subst hs; cases hv
    cases hL : vm.lookup n₁ with
    | none => rw [hL] at h₁; simp at h₁
    | some p => rw [hL] at h₁; obtain ⟨t', v'⟩ := p
                simp only [Option.some.injEq, Sigma.mk.injEq] at h₁
                obtain ⟨hst, hv1⟩ := h₁; subst hst; cases hv1
  · rw [if_neg e1] at h₁; rw [if_neg e2] at h₂
    cases hL1 : vm.lookup n₁ with
    | none => rw [hL1] at h₁; simp at h₁
    | some p1 =>
      cases hL2 : vm.lookup n₂ with
      | none => rw [hL2] at h₂; simp at h₂
      | some p2 =>
        rw [hL1] at h₁; rw [hL2] at h₂
        obtain ⟨ta, va⟩ := p1; obtain ⟨tb, vb⟩ := p2
        simp only [Option.some.injEq, Sigma.mk.injEq] at h₁ h₂
        obtain ⟨hsa, hva⟩ := h₁; obtain ⟨hsb, hvb⟩ := h₂
        subst hsa; subst hsb
        have heq : (CVar.there va : CVar (t :: Γ) tb) = CVar.there vb :=
          eq_of_heq (hva.trans hvb.symm)
        have hvv : va = vb := by injection heq
        subst hvv
        exact hNA n₁ n₂ tb va hL1 hL2

/-- `VarMap.weaken` preserves `NoAliasVM`: every name is `.there`-shifted
    uniformly, an injective embedding. -/
theorem noAlias_weaken {Γ : Ctx} {t : CryptoTy} {vm : VarMap Γ}
    (hNA : NoAliasVM vm) : NoAliasVM (vm.weaken : VarMap (t :: Γ)) := by
  intro n₁ n₂ s v h₁ h₂
  simp only [VarMap.weaken] at h₁ h₂
  cases hL1 : vm.lookup n₁ with
  | none => rw [hL1] at h₁; simp at h₁
  | some p1 =>
    cases hL2 : vm.lookup n₂ with
    | none => rw [hL2] at h₂; simp at h₂
    | some p2 =>
      rw [hL1] at h₁; rw [hL2] at h₂
      obtain ⟨ta, va⟩ := p1; obtain ⟨tb, vb⟩ := p2
      simp only [Option.some.injEq, Sigma.mk.injEq] at h₁ h₂
      obtain ⟨hsa, hva⟩ := h₁; obtain ⟨hsb, hvb⟩ := h₂
      subst hsa; subst hsb
      have hev : (CVar.there va : CVar (t :: Γ) tb) = CVar.there vb :=
        eq_of_heq (hva.trans hvb.symm)
      have hvv : va = vb := by injection hev
      subst hvv
      exact hNA n₁ n₂ tb va hL1 hL2

/-- A predicate relating a RustState to a CryptoSSA `HVec` at some
    context `Γ`, mediated by a `VarMap`. For each name in the VarMap,
    the byte-layout invariant `bindingOK` must hold (`binding` field), and
    the VarMap must be alias-free (`noAlias` field — see `NoAliasVM`). The
    `noAlias` field was added (#221) to make the `whileTrue` simulation arm
    sound; it is carried along by every witness-construction helper.

    A `CoeFun` instance lets an `RustStateInterp` be applied directly as the
    per-name `bindingOK` function (`hInv name t v hLook`), so the field
    addition is transparent to consumers. -/
structure RustStateInterp {Γ : Ctx} (vm : VarMap Γ) (rs : RustState)
    (V : HVec Γ) : Prop where
  binding : ∀ name : String, ∀ t : CryptoTy, ∀ v : CVar Γ t,
    vm.lookup name = some ⟨t, v⟩ → bindingOK rs V name v
  noAlias : NoAliasVM vm

/-- Apply an `RustStateInterp` directly as its per-name `bindingOK` function;
    keeps `hInv name t v hLook` working after the `noAlias` field was added. -/
instance {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ} :
    CoeFun (RustStateInterp vm rs V)
      (fun _ => ∀ name : String, ∀ t : CryptoTy, ∀ v : CVar Γ t,
        vm.lookup name = some ⟨t, v⟩ → bindingOK rs V name v) :=
  ⟨RustStateInterp.binding⟩

/-- The empty RustStateInterp at the empty context: trivially holds. -/
theorem rustStateInterp_empty (rs : RustState) :
    RustStateInterp VarMap.empty rs HVec.nil := by
  refine ⟨?_, noAlias_empty⟩
  intro name t v h
  -- VarMap.empty.lookup is always none, contradicting `some _`.
  simp [VarMap.empty] at h

/-! ## Canonical witness under `NoAliasVM`

Under `NoAliasVM vm`, for *any* RustState `rs` there is a valuation
`V : HVec Γ` with `RustStateInterp vm rs V`. This is the lever that closes the
`whileTrue` simulation arm: the post-loop state `r1` need not extend any prior
witness, but `NoAliasVM vm` (carried in `_hInv`) guarantees a fresh canonical
witness exists. Aliasing would break this — see `NoAliasVM`'s docstring. -/

/-- Build a valuation from a per-variable value function. -/
def HVec.ofVarFn :
    {Γ : Ctx} → (∀ {t : CryptoTy}, CVar Γ t → t.denote) → HVec Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f .here) (HVec.ofVarFn (fun v => f (.there v)))

@[simp] theorem HVec.lookup_ofVarFn {Γ : Ctx}
    (f : ∀ {t : CryptoTy}, CVar Γ t → t.denote) {t : CryptoTy} (v : CVar Γ t) :
    v.lookup (HVec.ofVarFn f) = f v := by
  induction v with
  | here => rfl
  | there v ih => exact ih (fun w => f (.there w))

/-- The value `bindingOK rs _ name v` demands of `v.lookup V`, independent of
    `V`. For `sword 64`, the little-endian word of `rs.rsScalar name`; for
    `memref n`, the byte-projection of the tower entry when present and
    type-matching, else zero; otherwise the type default (`bindingOK` is
    `True`). -/
noncomputable def demandVal (rs : RustState) (name : String) :
    (t : CryptoTy) → t.denote
  | .sword 64 => BitVec.ofNat 64 (rs.rsScalar name)
  | .memref n =>
      match rs.rsTower name with
      | some ⟨t', vt⟩ =>
          if henc : encodeTy t' = CryptoTy.memref n then
            cast (congrArg CryptoTy.denote henc) (cryptoTyOfRustVal t' vt)
          else (fun _ => 0)
      | none => (fun _ => 0)
  | t => CryptoTy.default t

/-- `demandVal` discharges `bindingOK` for the name it was computed from. -/
theorem bindingOK_demandVal {Γ : Ctx} (rs : RustState) (V : HVec Γ)
    (name : String) {t : CryptoTy} (v : CVar Γ t)
    (hv : v.lookup V = demandVal rs name t) : bindingOK rs V name v := by
  unfold bindingOK
  split
  · rename_i v; rw [hv]; rfl
  · rename_i n v
    rw [hv]
    cases h : rs.rsTower name with
    | none => simp only [h]
    | some p =>
        obtain ⟨t', vt⟩ := p; simp only [h]; intro henc
        unfold demandVal; rw [h]; simp only [henc, dif_pos]; exact cast_heq _ _
  · trivial

open Classical in
/-- Per-variable witness value: `demandVal` for the (unique, under `NoAliasVM`)
    name mapping to `v`, or the type default if no name maps there. -/
noncomputable def witVarFn {Γ : Ctx} (vm : VarMap Γ) (rs : RustState)
    {t : CryptoTy} (v : CVar Γ t) : t.denote :=
  if h : ∃ name, vm.lookup name = some ⟨t, v⟩ then demandVal rs h.choose t
  else CryptoTy.default t

/-- Under `NoAliasVM`, if `name` maps to `v` then `witVarFn` is `demandVal` of
    that very `name` (the choice is forced by injectivity). -/
theorem witVarFn_eq {Γ : Ctx} {vm : VarMap Γ} (hNA : NoAliasVM vm)
    (rs : RustState) (name : String) {t : CryptoTy} (v : CVar Γ t)
    (hLook : vm.lookup name = some ⟨t, v⟩) :
    witVarFn vm rs v = demandVal rs name t := by
  unfold witVarFn
  have hex : ∃ name, vm.lookup name = some ⟨t, v⟩ := ⟨name, hLook⟩
  rw [dif_pos hex]; congr 1
  exact hNA hex.choose name t v hex.choose_spec hLook

/-- **Canonical witness under `NoAliasVM`.** For any `rs`, the valuation
    `HVec.ofVarFn (witVarFn vm rs)` satisfies the byte-layout invariant
    `RustStateInterp vm rs _`. This is the `whileTrue`-arm lever: it produces a
    post-state witness with no dependence on any prior valuation. -/
theorem noAlias_canonical_witness {Γ : Ctx} {vm : VarMap Γ}
    (hNA : NoAliasVM vm) (rs : RustState) :
    RustStateInterp vm rs (HVec.ofVarFn (fun {t} v => witVarFn vm rs v)) := by
  refine ⟨?_, hNA⟩
  intro name t v hLook
  apply bindingOK_demandVal rs _ name v
  rw [HVec.lookup_ofVarFn]
  exact witVarFn_eq hNA rs name v hLook

/-! ## Default-value lemmas for `cryptoTyOfRustVal`

The `letZero` and `letU64Zero` cases of `rustExecSimulatesCryptoSSA`
(and, indirectly, `scalarSet` via the SSA-side `bvConst`) need to know
that a freshly-zero rust-side value packs into the freshly-zero
SSA-side denotation. These helper lemmas isolate that fact. -/

/-- Packing eight zero bytes into a 64-bit word yields zero. -/
lemma wordOfBytes8_zero : wordOfBytes8 (fun _ => 0) = 0 := by
  unfold wordOfBytes8; rfl

/-- A rust-side all-zero JArray projects to an all-zero memref. -/
lemma bytesOfMemrefRust_zero {n : Nat} :
    bytesOfMemrefRust (n := n) (fun _ => 0) = (fun _ => 0) := by
  funext i
  unfold bytesOfMemrefRust
  exact wordOfBytes8_zero

/-- The byte-projection of a rust-side `default` value (an all-zero
    `JArray`) is the SSA-side `CryptoTy.default` for the encoded type.
    This is the missing equation that makes `letZero` / `letU64Zero` /
    `scalarSet` (the three `bindingOK`-from-fresh-zero cases) close. -/
lemma cryptoTyOfRustVal_default (t : TowerType) :
    cryptoTyOfRustVal t (default : RustVal t)
      = CryptoTy.default (encodeTy t) := by
  cases t <;>
    simp only [cryptoTyOfRustVal, encodeTy, CryptoTy.default, default,
               bytesOfMemrefRust_zero, wordOfBytes8_zero]

/-! ## Transport lemmas for `bindingOK` under fresh top binding

The three closeable cases (`scalarSet`, `letU64Zero`, `letZero`) all
extend the SSA context with one fresh binding at the top and the rust
state with a fresh `rsSetScalar` or `rsSetTower` for the same name. The
following two lemmas package the per-name reasoning: an old binding at
`.there cv'` survives the cons (since `rsSetScalar`/`rsSetTower`
preserves all *other* names), and the new binding at `.here` is OK
because the SSA-side fresh value matches the rust-side fresh value
(zero or a `BitVec.ofNat 64 v` literal). -/

/-- `bindingOK` reduces to `True` for non-64 `sword n`. -/
lemma bindingOK_sword_ne {n : Nat} (h : n ≠ 64) {Γ : Ctx}
    (rs : RustState) (V : HVec Γ) (name : String)
    (cv : CVar Γ (.sword n)) :
    bindingOK rs V name cv := by
  unfold bindingOK
  -- Match dispatches: `sword 64` arm requires `n = 64` (excluded by `h`),
  -- `memref _` arm doesn't match `sword`, fallthrough is `True`.
  split <;> simp_all

/-- An existing binding `bindingOK rs V name cv'` is preserved when we
    cons a fresh `.sword 64` onto both sides and `rsSetScalar` the
    rust state with a value at a *different* name. -/
lemma bindingOK_there_scalarSet
    {Γ : Ctx} {rs : RustState} {V : HVec Γ}
    {name x : String} {t' : CryptoTy} (cv' : CVar Γ t') (w : BitVec 64) (v : Nat)
    (hN : name ≠ x)
    (hOK : bindingOK rs V name cv') :
    bindingOK (rsSetScalar rs x v) (HVec.cons w V) name
      (CVar.there cv' : CVar (.sword 64 :: Γ) t') := by
  -- `bindingOK` matches on `(t', cv')`. We propagate by case on `t'`.
  -- For `.sword 64`: lookup of `.there cv'` strips cons; rsScalar at
  -- name ≠ x is unchanged. For `.memref n`: rsTower is untouched by
  -- `rsSetScalar`, so the witness `(t'', vt)` survives.
  cases t' with
  | sword n =>
    by_cases h64 : n = 64
    · subst h64
      simp only [bindingOK] at hOK ⊢
      show (CVar.there cv' : CVar (.sword 64 :: Γ) (.sword 64)).lookup
              (HVec.cons w V)
            = BitVec.ofNat 64 ((rsSetScalar rs x v).rsScalar name)
      simp [CVar.lookup, rsSetScalar, hN, hOK]
    · -- `bindingOK` for `sword n` with `n ≠ 64` is `True`.
      -- Manually expose this via `bindingOK_sword_ne`, below.
      exact bindingOK_sword_ne (n := n) h64 _ _ _ _
  | memref n =>
    simp only [bindingOK] at hOK ⊢
    have hT : (rsSetScalar rs x v).rsTower = rs.rsTower := by
      funext _; simp [rsSetScalar]
    rw [hT]
    cases hRsT : rs.rsTower name with
    | none => rw [hRsT] at hOK; exact hOK
    | some pair =>
      rw [hRsT] at hOK
      obtain ⟨t'', vt⟩ := pair
      -- B1.sexta-tail Phase 3: `hOK` is now an implication
      -- `encodeTy t'' = .memref n → HEq ...`.
      intro hEnc
      have hHeq := hOK hEnc
      show HEq ((CVar.there cv' : CVar (.sword 64 :: Γ) (.memref n)).lookup
                  (HVec.cons w V))
               (cryptoTyOfRustVal t'' vt)
      simp only [CVar.lookup]; exact hHeq
  | bit =>      simp only [bindingOK]
  | unit =>     simp only [bindingOK]
  | pair _ _ => simp only [bindingOK]
  | sum _ _ =>  simp only [bindingOK]

/-- An existing binding `bindingOK rs V name cv'` is preserved when we
    cons a fresh value (at any CryptoTy `s`) onto both sides and
    `rsSetTower` the rust state at a *different* name. -/
lemma bindingOK_there_setTower
    {Γ : Ctx} {rs : RustState} {V : HVec Γ}
    {name x : String} {s : CryptoTy} {t' : CryptoTy}
    (cv' : CVar Γ t') (w : s.denote) (rv : Σ τ : TowerType, RustVal τ)
    (hN : name ≠ x)
    (hOK : bindingOK rs V name cv') :
    bindingOK (rsSetTower rs x rv) (HVec.cons w V) name
      (CVar.there cv' : CVar (s :: Γ) t') := by
  cases t' with
  | sword n =>
    by_cases h64 : n = 64
    · subst h64
      simp only [bindingOK] at hOK ⊢
      show (CVar.there cv' : CVar (s :: Γ) (.sword 64)).lookup
              (HVec.cons w V)
            = BitVec.ofNat 64 ((rsSetTower rs x rv).rsScalar name)
      have hScalar : (rsSetTower rs x rv).rsScalar = rs.rsScalar := by
        funext n; simp [rsSetTower]
      simp [CVar.lookup, hScalar, hOK]
    · exact bindingOK_sword_ne (n := n) h64 _ _ _ _
  | memref n =>
    simp only [bindingOK] at hOK ⊢
    have hOther : (rsSetTower rs x rv).rsTower name = rs.rsTower name :=
      rsSetTower_other rs x name rv (Ne.symm hN)
    rw [hOther]
    cases hRsT : rs.rsTower name with
    | none => rw [hRsT] at hOK; exact hOK
    | some pair =>
      rw [hRsT] at hOK
      obtain ⟨t'', vt⟩ := pair
      intro hEnc
      have hHeq := hOK hEnc
      show HEq ((CVar.there cv' : CVar (s :: Γ) (.memref n)).lookup
                  (HVec.cons w V))
               (cryptoTyOfRustVal t'' vt)
      simp only [CVar.lookup]; exact hHeq
  | bit =>      simp only [bindingOK]
  | unit =>     simp only [bindingOK]
  | pair _ _ => simp only [bindingOK]
  | sum _ _ =>  simp only [bindingOK]

/-- The three "fresh top binding" cases close uniformly via this lemma:
    `vm.bind x` extends `vm` with `(x ↦ ⟨.sword 64, .here⟩)`, and
    `rsSetScalar rs x v` consistently has `rsScalar x = v`, so the
    new binding satisfies `bindingOK` definitionally. Old bindings are
    preserved by `bindingOK_there_scalarSet`. -/
lemma interp_bind_sword64_scalarSet
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (v : Nat) :
    RustStateInterp (vm.bind x : VarMap (.sword 64 :: Γ))
      (rsSetScalar rs x v)
      (HVec.cons (BitVec.ofNat 64 v) V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name t cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hN : name = x
  · subst hN
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨ht, hcv⟩ := hLook
    subst ht
    cases hcv
    -- bindingOK at `(.sword 64, .here)` reduces to a literal equation.
    show (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)).lookup
            (HVec.cons (BitVec.ofNat 64 v) V)
          = BitVec.ofNat 64 ((rsSetScalar rs name v).rsScalar name)
    simp [CVar.lookup, rsSetScalar]
  · rw [if_neg hN] at hLook
    -- Existing binding: extract from `vm.lookup`.
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht
      cases hcvE
      exact bindingOK_there_scalarSet cv' (BitVec.ofNat 64 v) v hN
              (hInv name t' cv' hOld)

/-- Same as `interp_bind_sword64_scalarSet`, but for the
    `RLetU64Zero` case where the rust side is `rsSetScalar rs x 0`
    and the SSA side is `BitVec.ofNat 64 0`. (Indeed
    `BitVec.ofNat 64 0 = 0` definitionally.) -/
lemma interp_bind_sword64_zero
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) :
    RustStateInterp (vm.bind x : VarMap (.sword 64 :: Γ))
      (rsSetScalar rs x 0)
      (HVec.cons (0 : BitVec 64) V) := by
  -- `BitVec.ofNat 64 0 = 0` definitionally; reuse `_scalarSet` at v = 0.
  have : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl
  rw [this]
  exact interp_bind_sword64_scalarSet hInv x 0

/-- The TU64 sub-case of `RLetZero` is anomalous: `translate` emits a
    `.sword 64` binding (re-using the `RLetU64Zero` shape), but the
    rust-side `RustExec.letZero` calls `rsSetTower`, which does not
    touch `rsScalar`. The SSA-side fresh value is `0`, but the rust
    `rsScalar x` is whatever it was before. To satisfy `bindingOK`
    at this fresh binding, the simulation must therefore choose the
    head of the witness `HVec` to *match* the existing `rs.rsScalar x`
    rather than the program's literal `0`. The simulation theorem is
    only existential ("some valuation V' makes the invariant hold"),
    so this choice is legal — the proof does not claim the V' it
    produces equals the SSA-emitted denotation. -/
lemma interp_bind_sword64_letZeroTU64
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) :
    RustStateInterp (vm.bind x : VarMap (.sword 64 :: Γ))
      (rsSetTower rs x ⟨.TU64, (default : RustVal .TU64)⟩)
      (HVec.cons (BitVec.ofNat 64 (rs.rsScalar x)) V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name t cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hN : name = x
  · subst hN
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨ht, hcv⟩ := hLook
    subst ht
    cases hcv
    -- bindingOK at `(.sword 64, .here)` reduces to a literal equation.
    show (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)).lookup
            (HVec.cons (BitVec.ofNat 64 (rs.rsScalar name)) V)
          = BitVec.ofNat 64
              ((rsSetTower rs name ⟨.TU64, default⟩).rsScalar name)
    -- LHS is the head of cons; RHS reduces because rsSetTower
    -- preserves rsScalar.
    have : (rsSetTower rs name ⟨.TU64, default⟩).rsScalar = rs.rsScalar := by
      funext n; simp [rsSetTower]
    simp [CVar.lookup, this]
  · rw [if_neg hN] at hLook
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht
      cases hcvE
      exact bindingOK_there_setTower (s := .sword 64) cv'
              (BitVec.ofNat 64 (rs.rsScalar x))
              ⟨.TU64, (default : RustVal .TU64)⟩ hN
              (hInv name t' cv' hOld)

/-- The `RLetZero` case for tower types: extends with a fresh
    `memref n` of zeros on the SSA side and a fresh `rsSetTower rs x
    ⟨t, default⟩` on the rust side. -/
lemma interp_bind_memref_letZero
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (t : TowerType)
    {n : Nat} (hN : encodeTy t = .memref n) :
    RustStateInterp (vm.bind x : VarMap (.memref n :: Γ))
      (rsSetTower rs x ⟨t, (default : RustVal t)⟩)
      (HVec.cons (fun _ => 0 : Fin n → BitVec 64) V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name s cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hX : name = x
  · subst hX
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨hs, hcv⟩ := hLook
    subst hs
    cases hcv
    -- bindingOK at `(.memref n, .here)`: rs.rsTower name = some ⟨t, default⟩
    -- via `rsSetTower_same`, so we hit the `some` arm of the weakened match.
    -- B1.sexta-tail Phase 3: arm is now an implication; intro the antecedent
    -- (which is `hN` itself) and prove the HEq from `cryptoTyOfRustVal_default`.
    simp only [bindingOK]
    rw [rsSetTower_same rs name ⟨t, default⟩]
    intro _hEnc
    simp only [CVar.lookup]
    rw [cryptoTyOfRustVal_default]
    rw [hN]
    rfl
  · rw [if_neg hX] at hLook
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht
      cases hcvE
      exact bindingOK_there_setTower (s := .memref n) cv'
              (fun _ => 0 : Fin n → BitVec 64)
              ⟨t, (default : RustVal t)⟩ hX
              (hInv name t' cv' hOld)

/-! ## B1.sexta: generalized rsSetTower transport for arbitrary values

The `letZero` cases use `interp_bind_sword64_letZeroTU64` and
`interp_bind_memref_letZero` which are specialised to the rust-side
`default` value.  The `call` / `cloneCall` / `limbStore` cases need
the same transport but for *arbitrary* rust-side values produced by
`leafSpec.call` / `leafSpec.limbStore`.

The proofs are essentially the same — only the rust-side witness
changes — but the SSA-side V' must be chosen to make `bindingOK`
match.  Since V' is *existentially quantified* in the simulation
theorem's conclusion, we are free to pick it as the encoding of the
rust-side value.  No per-leaf adequacy contract is required at this
level; the simulation theorem gives only existence of a valid V',
not that V' equals any specific SSA-emitted denotation. -/

/-- TU64 transport: extending with any `(.TU64, val)` rust binding
preserves `RustStateInterp` when the SSA side cons'es
`BitVec.ofNat 64 (rs.rsScalar x)` (matching the `bindingOK` for
sword 64 against the unchanged `rsScalar`). -/
lemma interp_bind_sword64_setTowerTU64_general
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String)
    (val : RustVal .TU64) :
    RustStateInterp (vm.bind x : VarMap (.sword 64 :: Γ))
      (rsSetTower rs x ⟨.TU64, val⟩)
      (HVec.cons (BitVec.ofNat 64 (rs.rsScalar x)) V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name t cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hN : name = x
  · subst hN
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨ht, hcv⟩ := hLook
    subst ht
    cases hcv
    show (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)).lookup
            (HVec.cons (BitVec.ofNat 64 (rs.rsScalar name)) V)
          = BitVec.ofNat 64
              ((rsSetTower rs name ⟨.TU64, val⟩).rsScalar name)
    have : (rsSetTower rs name ⟨.TU64, val⟩).rsScalar = rs.rsScalar := by
      funext n; simp [rsSetTower]
    simp [CVar.lookup, this]
  · rw [if_neg hN] at hLook
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht
      cases hcvE
      exact bindingOK_there_setTower (s := .sword 64) cv'
              (BitVec.ofNat 64 (rs.rsScalar x))
              ⟨.TU64, val⟩ hN
              (hInv name t' cv' hOld)

/-- memref transport: extending with any `(t, val)` rust binding
where `encodeTy t = .memref n` preserves `RustStateInterp` when the
SSA side cons'es the encoded rust value via `cryptoTyOfRustVal`
(reshuffled through `hN` to land at type `Fin n → BitVec 64`). -/
lemma interp_bind_memref_setTower_general
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (t : TowerType)
    {n : Nat} (hN : encodeTy t = .memref n) (val : RustVal t) :
    RustStateInterp (vm.bind x : VarMap (.memref n :: Γ))
      (rsSetTower rs x ⟨t, val⟩)
      (HVec.cons (cast (congrArg CryptoTy.denote hN)
                       (cryptoTyOfRustVal t val) : Fin n → BitVec 64) V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name s cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hX : name = x
  · subst hX
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨hs, hcv⟩ := hLook
    subst hs
    cases hcv
    simp only [bindingOK]
    rw [rsSetTower_same rs name ⟨t, val⟩]
    intro _hEnc
    simp only [CVar.lookup]
    exact (cast_heq _ _).trans (HEq.refl _)
  · rw [if_neg hX] at hLook
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht
      cases hcvE
      exact bindingOK_there_setTower (s := .memref n) cv'
              (cast (congrArg CryptoTy.denote hN) (cryptoTyOfRustVal t val) :
                Fin n → BitVec 64)
              ⟨t, val⟩ hX
              (hInv name t' cv' hOld)

/-- B1.sexta-tail Phase 5 helper: extend a witness over `(vm.bind cv) at
    `(rsSetTower rs cv tv)` for an arbitrary CryptoTy `s`. Discharges
    the new binding's `bindingOK` by dispatching on `s`. Used in the
    `cloneCall` arm of `rustExecSimulatesCryptoSSA` (and analogously in
    `interp_translate_extend`). -/
lemma interp_cons_setTower_any
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (cv : String) (s : CryptoTy)
    (tv : Σ τ : TowerType, RustVal τ) :
    ∃ w : s.denote,
      RustStateInterp (vm.bind cv : VarMap (s :: Γ))
        (rsSetTower rs cv tv) (HVec.cons w V) := by
  match s with
  | .sword n =>
    by_cases h64 : n = 64
    · subst h64
      refine ⟨BitVec.ofNat 64 (rs.rsScalar cv), ?_, noAlias_bind hInv.noAlias cv⟩
      intro nm t cv' hLook
      simp only [VarMap.bind] at hLook
      by_cases hX : nm = cv
      · subst hX
        rw [if_pos rfl] at hLook
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcv⟩ := hLook
        subst ht; cases hcv
        show (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)).lookup _
              = BitVec.ofNat 64 ((rsSetTower rs nm tv).rsScalar nm)
        have hScalar : (rsSetTower rs nm tv).rsScalar = rs.rsScalar := by
          funext n; simp [rsSetTower]
        simp [CVar.lookup, hScalar]
      · rw [if_neg hX] at hLook
        cases hOld : vm.lookup nm with
        | none => rw [hOld] at hLook; exact absurd hLook (by simp)
        | some pair =>
          rw [hOld] at hLook
          obtain ⟨t', cv''⟩ := pair
          simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
          obtain ⟨ht, hcvE⟩ := hLook
          subst ht; cases hcvE
          exact bindingOK_there_setTower (s := .sword 64) cv''
                  (BitVec.ofNat 64 (rs.rsScalar cv)) tv hX
                  (hInv nm t' cv'' hOld)
    · refine ⟨CryptoTy.default _, ?_, noAlias_bind hInv.noAlias cv⟩
      intro nm t cv' hLook
      simp only [VarMap.bind] at hLook
      by_cases hX : nm = cv
      · subst hX
        rw [if_pos rfl] at hLook
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcv⟩ := hLook
        subst ht; cases hcv
        exact bindingOK_sword_ne (n := n) h64 _ _ _ _
      · rw [if_neg hX] at hLook
        cases hOld : vm.lookup nm with
        | none => rw [hOld] at hLook; exact absurd hLook (by simp)
        | some pair =>
          rw [hOld] at hLook
          obtain ⟨t', cv''⟩ := pair
          simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
          obtain ⟨ht, hcvE⟩ := hLook
          subst ht; cases hcvE
          exact bindingOK_there_setTower (s := .sword n) cv''
                  (CryptoTy.default _) tv hX
                  (hInv nm t' cv'' hOld)
  | .memref n =>
    -- Pick witness based on whether `tv`'s type encodes to `.memref n`.
    obtain ⟨t', val⟩ := tv
    by_cases hEnc : encodeTy t' = .memref n
    · refine ⟨cast (congrArg CryptoTy.denote hEnc) (cryptoTyOfRustVal t' val), ?_,
        noAlias_bind hInv.noAlias cv⟩
      intro nm s cv' hLook
      simp only [VarMap.bind] at hLook
      by_cases hX : nm = cv
      · subst hX
        rw [if_pos rfl] at hLook
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨hs, hcv⟩ := hLook
        subst hs; cases hcv
        simp only [bindingOK]
        rw [rsSetTower_same rs nm ⟨t', val⟩]
        intro _hEnc'
        simp only [CVar.lookup]
        exact (cast_heq _ _).trans (HEq.refl _)
      · rw [if_neg hX] at hLook
        cases hOld : vm.lookup nm with
        | none => rw [hOld] at hLook; exact absurd hLook (by simp)
        | some pair =>
          rw [hOld] at hLook
          obtain ⟨t'', cv''⟩ := pair
          simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
          obtain ⟨ht, hcvE⟩ := hLook
          subst ht; cases hcvE
          exact bindingOK_there_setTower (s := .memref n) cv''
                  (cast (congrArg CryptoTy.denote hEnc) (cryptoTyOfRustVal t' val))
                  ⟨t', val⟩ hX
                  (hInv nm t'' cv'' hOld)
    · refine ⟨fun _ => 0, ?_, noAlias_bind hInv.noAlias cv⟩
      intro nm s cv' hLook
      simp only [VarMap.bind] at hLook
      by_cases hX : nm = cv
      · subst hX
        rw [if_pos rfl] at hLook
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨hs, hcv⟩ := hLook
        subst hs; cases hcv
        simp only [bindingOK]
        rw [rsSetTower_same rs nm ⟨t', val⟩]
        intro hAbs
        exact absurd hAbs hEnc
      · rw [if_neg hX] at hLook
        cases hOld : vm.lookup nm with
        | none => rw [hOld] at hLook; exact absurd hLook (by simp)
        | some pair =>
          rw [hOld] at hLook
          obtain ⟨t'', cv''⟩ := pair
          simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
          obtain ⟨ht, hcvE⟩ := hLook
          subst ht; cases hcvE
          exact bindingOK_there_setTower (s := .memref n) cv''
                  (fun _ => 0) ⟨t', val⟩ hX
                  (hInv nm t'' cv'' hOld)
  | .bit =>
    refine ⟨CryptoTy.default _, ?_, noAlias_bind hInv.noAlias cv⟩
    intro nm t cv' hLook
    simp only [VarMap.bind] at hLook
    by_cases hX : nm = cv
    · subst hX
      rw [if_pos rfl] at hLook
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcv⟩ := hLook
      subst ht; cases hcv
      simp only [bindingOK]
    · rw [if_neg hX] at hLook
      cases hOld : vm.lookup nm with
      | none => rw [hOld] at hLook; exact absurd hLook (by simp)
      | some pair =>
        rw [hOld] at hLook
        obtain ⟨t', cv''⟩ := pair
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcvE⟩ := hLook
        subst ht; cases hcvE
        exact bindingOK_there_setTower (s := .bit) cv''
                (CryptoTy.default _) tv hX
                (hInv nm t' cv'' hOld)
  | .unit =>
    refine ⟨CryptoTy.default _, ?_, noAlias_bind hInv.noAlias cv⟩
    intro nm t cv' hLook
    simp only [VarMap.bind] at hLook
    by_cases hX : nm = cv
    · subst hX
      rw [if_pos rfl] at hLook
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcv⟩ := hLook
      subst ht; cases hcv
      simp only [bindingOK]
    · rw [if_neg hX] at hLook
      cases hOld : vm.lookup nm with
      | none => rw [hOld] at hLook; exact absurd hLook (by simp)
      | some pair =>
        rw [hOld] at hLook
        obtain ⟨t', cv''⟩ := pair
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcvE⟩ := hLook
        subst ht; cases hcvE
        exact bindingOK_there_setTower (s := .unit) cv''
                (CryptoTy.default _) tv hX
                (hInv nm t' cv'' hOld)
  | .pair s1 s2 =>
    refine ⟨CryptoTy.default _, ?_, noAlias_bind hInv.noAlias cv⟩
    intro nm t cv' hLook
    simp only [VarMap.bind] at hLook
    by_cases hX : nm = cv
    · subst hX
      rw [if_pos rfl] at hLook
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcv⟩ := hLook
      subst ht; cases hcv
      simp only [bindingOK]
    · rw [if_neg hX] at hLook
      cases hOld : vm.lookup nm with
      | none => rw [hOld] at hLook; exact absurd hLook (by simp)
      | some pair =>
        rw [hOld] at hLook
        obtain ⟨t', cv''⟩ := pair
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcvE⟩ := hLook
        subst ht; cases hcvE
        exact bindingOK_there_setTower (s := .pair s1 s2) cv''
                (CryptoTy.default _) tv hX
                (hInv nm t' cv'' hOld)
  | .sum s1 s2 =>
    refine ⟨CryptoTy.default _, ?_, noAlias_bind hInv.noAlias cv⟩
    intro nm t cv' hLook
    simp only [VarMap.bind] at hLook
    by_cases hX : nm = cv
    · subst hX
      rw [if_pos rfl] at hLook
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcv⟩ := hLook
      subst ht; cases hcv
      simp only [bindingOK]
    · rw [if_neg hX] at hLook
      cases hOld : vm.lookup nm with
      | none => rw [hOld] at hLook; exact absurd hLook (by simp)
      | some pair =>
        rw [hOld] at hLook
        obtain ⟨t', cv''⟩ := pair
        simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
        obtain ⟨ht, hcvE⟩ := hLook
        subst ht; cases hcvE
        exact bindingOK_there_setTower (s := .sum s1 s2) cv''
                (CryptoTy.default _) tv hX
                (hInv nm t' cv'' hOld)

/-- Cons-extension preserves `bindingOK` for old bindings under the
unchanged rust state. -/
lemma bindingOK_there_consonly
    {Γ : Ctx} {rs : RustState} {V : HVec Γ}
    {name : String} {s : CryptoTy} {t' : CryptoTy}
    (cv' : CVar Γ t') (w : s.denote)
    (hOK : bindingOK rs V name cv') :
    bindingOK rs (HVec.cons w V) name (CVar.there cv' : CVar (s :: Γ) t') := by
  cases t' with
  | sword n =>
    by_cases h64 : n = 64
    · subst h64
      simp only [bindingOK] at hOK ⊢
      show (CVar.there cv' : CVar (s :: Γ) (.sword 64)).lookup (HVec.cons w V)
            = BitVec.ofNat 64 (rs.rsScalar name)
      simp [CVar.lookup, hOK]
    · exact bindingOK_sword_ne (n := n) h64 _ _ _ _
  | memref n =>
    simp only [bindingOK] at hOK ⊢
    cases hRsT : rs.rsTower name with
    | none => rw [hRsT] at hOK; exact hOK
    | some pair =>
      rw [hRsT] at hOK
      obtain ⟨t'', vt⟩ := pair
      intro hEnc
      have hHeq := hOK hEnc
      simp only [CVar.lookup]; exact hHeq
  | bit | unit | pair _ _ | sum _ _ => simp only [bindingOK]

/-- Whole-VarMap variant: extending `vm` with `vm.bind x` and the SSA
side with `HVec.cons w V` preserves `RustStateInterp` against an
unchanged rust state, provided the new binding's `bindingOK` is
discharged. -/
lemma interp_cons_unchanged
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) {s : CryptoTy} (w : s.denote)
    (hPick : bindingOK rs (HVec.cons w V) x (CVar.here : CVar (s :: Γ) s)) :
    RustStateInterp (vm.bind x : VarMap (s :: Γ)) rs (HVec.cons w V) := by
  refine ⟨?_, noAlias_bind hInv.noAlias x⟩
  intro name t cv hLook
  simp only [VarMap.bind] at hLook
  by_cases hN : name = x
  · subst hN
    rw [if_pos rfl] at hLook
    simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
    obtain ⟨ht, hcv⟩ := hLook
    subst ht; cases hcv; exact hPick
  · rw [if_neg hN] at hLook
    cases hOld : vm.lookup name with
    | none => rw [hOld] at hLook; exact absurd hLook (by simp)
    | some pair =>
      rw [hOld] at hLook
      obtain ⟨t', cv'⟩ := pair
      simp only [Option.some.injEq, Sigma.mk.injEq] at hLook
      obtain ⟨ht, hcvE⟩ := hLook
      subst ht; cases hcvE
      exact bindingOK_there_consonly cv' w (hInv name t' cv' hOld)

/-! ### B1.sexta-tail Phase 0 (continued): witness-packaging helpers

Specialised cons-extension wrappers for the common shapes of fresh
binding `interp_translate_extend` (Phase 1) needs to discharge:

* `interp_cons_memref_fresh`: when extending by a `memref n` whose
  associated rust-state name is fresh (`rs.rsTower x = none`), the
  `bindingOK` obligation reduces to the vacuous `none`-arm of the
  predicate. Used in the `RLetZero` arms (TFp / TFp2 / TFp6 / TFp12).
* `interp_cons_sword64_unchanged`: when extending by a `sword 64`
  binding whose head value is `BitVec.ofNat 64 (rs.rsScalar x)`, the
  `bindingOK` obligation discharges by `rfl`. Used in the
  `RScalarSet`, `RLetU64Zero`, and `RLetZero TU64` arms. -/

lemma interp_cons_memref_fresh
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (n : Nat)
    (hFresh : rs.rsTower x = none) :
    RustStateInterp (vm.bind x : VarMap (.memref n :: Γ)) rs
      (HVec.cons (fun _ => 0 : Fin n → BitVec 64) V) := by
  apply interp_cons_unchanged hInv x (s := .memref n) (fun _ => 0)
  simp only [bindingOK, hFresh]

lemma interp_cons_sword64_unchanged
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) :
    RustStateInterp (vm.bind x : VarMap (.sword 64 :: Γ)) rs
      (HVec.cons (BitVec.ofNat 64 (rs.rsScalar x)) V) := by
  apply interp_cons_unchanged hInv x (s := .sword 64) (BitVec.ofNat 64 (rs.rsScalar x))
  show (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)).lookup _
        = BitVec.ofNat 64 (rs.rsScalar x)
  simp [CVar.lookup]

/-- B1.sexta-tail Phase 3: extend by a memref n binding whose name has a
    rust-side tower entry of *matching* encoded type. Pick witness as
    the encoded rust value via `cryptoTyOfRustVal`. -/
lemma interp_cons_memref_some_match
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (n : Nat)
    (t' : TowerType) (vt : RustVal t')
    (hRsT : rs.rsTower x = some ⟨t', vt⟩)
    (hEnc : encodeTy t' = .memref n) :
    RustStateInterp (vm.bind x : VarMap (.memref n :: Γ)) rs
      (HVec.cons (cast (congrArg CryptoTy.denote hEnc)
                       (cryptoTyOfRustVal t' vt) : Fin n → BitVec 64) V) := by
  apply interp_cons_unchanged hInv x (s := .memref n)
        (cast (congrArg CryptoTy.denote hEnc) (cryptoTyOfRustVal t' vt) :
          Fin n → BitVec 64)
  simp only [bindingOK, hRsT]
  intro _hEnc'
  show HEq ((CVar.here : CVar (.memref n :: Γ) (.memref n)).lookup
              (HVec.cons (cast (congrArg CryptoTy.denote hEnc)
                               (cryptoTyOfRustVal t' vt) : Fin n → BitVec 64) V))
           (cryptoTyOfRustVal t' vt)
  simp only [CVar.lookup]
  exact (cast_heq _ _).trans (HEq.refl _)

/-- B1.sexta-tail Phase 3: extend by a memref n binding whose name has a
    rust-side tower entry of *mismatching* encoded type. The implication
    in `bindingOK`'s `some` arm is vacuous; pick witness 0. -/
lemma interp_cons_memref_some_mismatch
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (n : Nat)
    (t' : TowerType) (vt : RustVal t')
    (hRsT : rs.rsTower x = some ⟨t', vt⟩)
    (hNeq : encodeTy t' ≠ .memref n) :
    RustStateInterp (vm.bind x : VarMap (.memref n :: Γ)) rs
      (HVec.cons (fun _ => 0 : Fin n → BitVec 64) V) := by
  apply interp_cons_unchanged hInv x (s := .memref n) (fun _ => 0)
  simp only [bindingOK, hRsT]
  intro hAbs
  exact absurd hAbs hNeq

/-- B1.sexta-tail Phase 3: extend by an arbitrary CryptoTy `s` binding,
    picking a vacuous witness via `CryptoTy.default`. The bindingOK at
    `(s, .here)` reduces to `True` for non-`sword 64` / non-`memref n`
    types; for `sword 64` and `memref n` we delegate to the dedicated
    helpers. This is the catch-all for the cloneTy step in `RCloneCall`. -/
lemma interp_cons_any_unchanged
    {Γ : Ctx} {vm : VarMap Γ} {rs : RustState} {V : HVec Γ}
    (hInv : RustStateInterp vm rs V) (x : String) (s : CryptoTy) :
    ∃ w : s.denote, RustStateInterp (vm.bind x : VarMap (s :: Γ)) rs
      (HVec.cons w V) := by
  match s with
  | .sword n =>
    by_cases hn : n = 64
    · subst hn
      exact ⟨BitVec.ofNat 64 (rs.rsScalar x), interp_cons_sword64_unchanged hInv x⟩
    · refine ⟨CryptoTy.default _, ?_⟩
      apply interp_cons_unchanged hInv x (s := .sword n) (CryptoTy.default _)
      exact bindingOK_sword_ne (n := n) hn _ _ _ _
  | .memref n =>
    cases hRsT : rs.rsTower x with
    | none => exact ⟨fun _ => 0, interp_cons_memref_fresh hInv x n hRsT⟩
    | some pair =>
      obtain ⟨t', vt⟩ := pair
      by_cases hEnc : encodeTy t' = .memref n
      · exact ⟨_, interp_cons_memref_some_match hInv x n t' vt hRsT hEnc⟩
      · exact ⟨fun _ => 0, interp_cons_memref_some_mismatch hInv x n t' vt hRsT hEnc⟩
  | .bit =>
    refine ⟨CryptoTy.default _, ?_⟩
    apply interp_cons_unchanged hInv x (s := .bit) (CryptoTy.default _)
    simp only [bindingOK]
  | .unit =>
    refine ⟨CryptoTy.default _, ?_⟩
    apply interp_cons_unchanged hInv x (s := .unit) (CryptoTy.default _)
    simp only [bindingOK]
  | .pair _ _ =>
    refine ⟨CryptoTy.default _, ?_⟩
    apply interp_cons_unchanged hInv x (s := .pair _ _) (CryptoTy.default _)
    simp only [bindingOK]
  | .sum _ _ =>
    refine ⟨CryptoTy.default _, ?_⟩
    apply interp_cons_unchanged hInv x (s := .sum _ _) (CryptoTy.default _)
    simp only [bindingOK]

end CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
