/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle


@[expose] public section
set_option autoImplicit false

/-!
# Front-general SCALAR preservation (`denote = semScalar`) — straight-line core

The SIMD path (`TranslateDialectVsimdDenote.translateDialectControlV_denote`) is
the only front with a **front-general** preservation homomorphism: for any covered
`vsimd` body, the emitted `Com catCryptDialect` prefix denotes exactly the body's
`SimdOp`-fold semantics, symbolically over all inputs. This module builds the
**scalar** analogue over the straight-line fragment the point-op / field bricks
use: `RScalarSetExpr`, the opaque leaf-call arm (`RCall`), the dynamic-index array
arms (`RArrLoad` / `RArrStore`), and their `RSeq` / `RBlock` / `RSkip` closure.

Three new pieces (the scalar twins of `semV` / `ConsistentV`):

* `SEnvScalar` — a per-name partial environment of *heterogeneously typed* values
  `(t : CryptoTy) × ⟦t⟧` (the scalar path threads `.sword w` words, `.memref n`
  arrays, and opaque `extCall` results, so — unlike the mono-typed 128-bit
  `SEnv` — the value universe is the full `CryptoTy` denotation);
* `semScalar : LowCT → SEnvScalar → Option SEnvScalar` — the pure operational
  semantics of the covered scalar arms, each op reading its operands from the env
  and binding its destination to the SAME waist the front's emitted
  `catCryptDialect` op denotes by (`extCall ↦ CryptoTy.default`, `memrefGetDyn ↦
  memGetDyn`, `memrefSetDyn ↦ memSetDyn`, an `SExpr` word-op fold for
  `RScalarSetExpr`);
* `ConsistentS vm V env` — every name's `env` value is exactly the slot it
  resolves to in the `Γ`-valuation `V` (the heterogeneous twin of `ConsistentV`).

The theorem `translateDialectControl_denote` is proved by induction on
the straight-line coverage `IsCoveredS`, its `rSeq` arm discharging the
per-concatenation homomorphism `denote (front (a ++ b)) = denote (front b) ∘
denote (front a)` via `ComCont.comp o₁.cont o₂.cont` — the exact shape the SIMD
`rSeq` arm uses. Every single-binding arm reduces to the type-generic one-op step
`scalar_step` (the heterogeneous twin of `vsimd_step`). It is stated in the same
shape as the SIMD theorem, so it extends to more arms by adding coverage
constructors.

## Main results

* `translateDialectFull_denote`, `translateDialectControl_denote_ctl` — the emitted
  `Com` prefix denotes the `semScalar` semantics of an `IsCoveredS` /
  `IsCoveredSCtl` body
* `translateDialectFull_denoteWith`, `translateDialectControl_denote_ctlWith` — for
  every leaf oracle `ls`, the emitted prefix under `catCryptDenoteWith ls` denotes
  the `semScalarL ls` semantics; the two theorems above are their instances at
  `defaultLeaf`
* `argVals_of_resolve` — under `ConsistentS`, the argument values an emitted
  `extCall` passes its oracle are the values `semScalarL` reads from the environment

## Scope of this file

`IsCoveredS` / the proved theorem cover the whole straight-line mechanical
fragment: the `RSeq` / `RBlock` / `RSkip` closure; the const/zero scalar binds
(`RScalarSet`, `RLetU64Zero`); every opaque leaf-call arm (`RCall`,
`RCallDstThreaded`, `RTupleLoad`, the two-dest `RCallSwap` and `RCloneCall`, the
N-dest `RCallN`); the dynamic-index array **load**/**store** arms (`RArrLoad` via
`memGetDyn`, `RArrStore` via `memSetDyn`) and their literal-index twins
(`RArrLoadLit`/`RArrStoreLit`, a `bvConst` index temp + the same read or write on a
`TArr _ .TU64` word array, opaque on other slot and array types); the constant-time word select `RSelect` (the comparison
select, §5e′, opaque on other slot types); the memref limb write `RLimbStore` (a
weaken-step + a `memrefSet` bind on a bound memref destination; on an unbound
destination the literal slot, a `bvConst` bind + an `extCall (limbLitLeafName idx)`
bind at the leaf oracle); and the contract assertion `RAssert` (no
emission, identity waist — §4b). Every single-binding arm reduces to `scalar_step`; the
multi-binding arms (`RLetU64Zero`, `RCallSwap`, `RCloneCall`, `RLimbStore`,
`RCallN`) compose per-bind via `ComCont.comp` along the `RSeq` spine (`RCallN` by
induction on its dest list, generalizing the context).

The scalar-`SExpr` assignment (`RScalarSetExpr`) — the point-op brick route — is
proved over its `srcClean` fragment (`SVar` / `SLit` / `SAdd` / `SSub` /
`SMul` / `SAnd` / `SXor` / `SShl` / `SShr` / `SMulHiU` over non-`__sx` source
variables and `< 2^64` literals — the full alphabet of the Keccak-f1600 round
bodies and the secp256k1 `feMul` brick). It rests on the `SExpr`-recursion
homomorphism `lowerSExpr_denote` (§5f): by induction on `SExpr`, the front's
fresh-temp `varBind` chain denotes its env-level mirror `semLowerSExpr`, and its
result slot resolves to the closed-form word evaluator `SExpr.evalBV (envReader
env) e`. The fresh temporaries never collide with a source read (`tmpName`
injectivity — proved here via a decimal digit round-trip, §2b — plus the
`OnlyTmpBelow` / `ResultOK` bookkeeping). The shift arms case the front's
immediate-vs-variable amount selection (`bvShiftL 64 k` on a literal `SLit k`,
`bvShiftLV 64` otherwise), reconciled with `evalBV`'s uniform
`<<< (amount).toNat` through `srcClean`'s `k < 2^64` literal bound; `SMulHiU`
closes through the `mulHiC`↔`sexprMulHiU` bridge (`mulHiC_eq_sexprMulHiU`). The
remaining `SExpr` nodes (the signed `SAsr` / `SMulS` / `SMulHiS`, the tower read
`SLimb`, `SLt`) stay excluded from `srcClean` (no jasmin lowering or signed
semantics the covered kernels don't use).

**Stage 2 (§8) is closed**: the control arms `RFor` (bounded meta-unroll) and
`RIfNz` (φ-merge) are proved, so the preservation homomorphism
(`translateDialectControl_denote_ctl`) covers the full control-extended
fragment `IsCoveredSCtl` — arm-for-arm the shape of
`TranslateDialectDirectControl.IsCoveredCtl` (with the `srcClean` side
condition on `RScalarSetExpr`, exactly as `IsCoveredS` refines `IsCovered`).

`IsCoveredS` is the full straight-line `IsCovered`; `IsCoveredSCtl` adds
`RFor` + `RIfNz` on top.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr callNLeafName)

/-! ## 1. Heterogeneously-typed scalar environment -/

/-- A per-name partial environment of typed scalar values. Each bound name maps
    to a dependent pair `(t : CryptoTy) × ⟦t⟧` — the value together with the
    `CryptoTy` it inhabits — so the same env can carry `.sword w` words, `.memref
    n` arrays, and opaque `extCall` results side by side (the scalar path is
    heterogeneously typed, unlike the mono-128-bit `SEnv`). -/
abbrev SEnvScalar := String → Option ((t : CryptoTy) × ⟦t⟧)

/-- Update a name in an `SEnvScalar` with a value of type `t`. -/
def SEnvScalar.upd (env : SEnvScalar) (name : String) {t : CryptoTy} (val : ⟦t⟧) :
    SEnvScalar :=
  fun s => if s = name then some ⟨t, val⟩ else env s

/-- Consistency between a `VarMap` at `Γ`, a `Γ`-valuation `V`, and an
    `SEnvScalar`: every name's env value is exactly the typed slot it resolves to
    in `V` (or `none` if the name is unbound in the `VarMap`). The heterogeneous
    twin of `ConsistentV`. -/
def ConsistentS {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar) : Prop :=
  ∀ s : String,
    (vm.lookup s).map (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))
      = env s

/-- Entry consistency at the empty context: the empty varmap, the empty
    valuation, and the everywhere-`none` env are consistent. Every
    translation pipeline starts here, so the entry `ConsistentS` hypothesis
    of the preservation theorem is discharged for free at top level. -/
theorem consistentS_empty :
    ConsistentS VarMap.empty (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx))
      (fun _ => none) :=
  fun _ => rfl

/-- Read a tracked output's value out of a `ConsistentS` state: if the varmap
    tracks `name` at slot `w : CVar Γ t` and the env carries `val` at the same
    type `t`, then the valuation's slot value IS `val`. The single-name
    projection that lets a caller convert "the source semantics left `val` in
    `name`" into "the emitted program's return slot holds `val`". -/
theorem ConsistentS.lookup_eq {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) {name : String} {t : CryptoTy}
    {w : CVar Γ t} {val : ⟦t⟧}
    (hw : vm.lookup name = some ⟨t, w⟩) (hval : env name = some ⟨t, val⟩) :
    (toVIRVar w).lookup V = val := by
  have h := hc name
  rw [hw, hval] at h
  simpa using h

/-! ## 2. The type-generic single-op step (shared across all single-binding arms)

The scalar analogue of `vsimd_step`, but **type-generic** in the bound slot's
`CryptoTy` `t` (the SIMD twin was pinned to `.sword 128`): emitting a `varBind`
of an expression `e : Expr … Γ t` over the entry valuation `V` extends
consistency by binding `dst` to `e.denote V`, and the emitted prefix, applied to
any tail, denotes that tail at the extended valuation. -/

/-- One op step at the leaf oracle `ls`: `ComCont.varBind e` binds `dst` to the
    denotation of `e` under `catCryptDenoteWith ls`, extending `ConsistentS`, and
    denotes any tail at the extended valuation. Common core of every single-binding
    scalar arm (`RCall`, the memref `RArrLoad`/`RArrStore`, each `SExpr` node) — they
    differ only in `e`. -/
theorem scalar_stepWith (ls : SemLeafSpec) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) :
    ConsistentS (vm.bind dst)
        (V.extend (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ e V))
        (env.upd dst (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ e V)) ∧
    ∀ {s : CryptoTy} (tail : Com catCryptDialect (t :: Γ) s),
      ∃ com, (ComCont.varBind e) tail = some com ∧
        @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
          = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail
              (V.extend (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ e V)) := by
  refine ⟨?_, ?_⟩
  · intro s
    by_cases hsd : s = dst
    · subst hsd
      simp only [VarMap.bind, SEnvScalar.upd]
      rfl
    · simp only [VarMap.bind, SEnvScalar.upd, if_neg hsd]
      rw [← hc s]
      cases hl : vm.lookup s with
      | none => rfl
      | some p =>
          obtain ⟨t', v⟩ := p
          rfl
  · intro s tail
    exact ⟨Com.var e tail, rfl, rfl⟩

/-- One op step: `ComCont.varBind e` binds `dst` to `e.denote V`, extending
    `ConsistentS`, and denotes any tail at the extended valuation
    (`scalar_stepWith` at `defaultLeaf`). -/
theorem scalar_step {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) :
    ConsistentS (vm.bind dst) (V.extend (e.denote V)) (env.upd dst (e.denote V)) ∧
    ∀ {s : CryptoTy} (tail : Com catCryptDialect (t :: Γ) s),
      ∃ com, (ComCont.varBind e) tail = some com ∧
        com.denote V = tail.denote (V.extend (e.denote V)) := by
  have h := scalar_stepWith defaultLeaf vm V env hc dst e
  rwa [catCryptDenoteWith_default] at h

/-- Weakening step (the un-named twin of `scalar_step`'s consistency half): a
    `varBind` that grows the context by an *anonymous* fresh slot (`vm.weaken`,
    not `vm.bind`) keeps every existing name consistent — the new slot shifts
    each bound `CVar` by `.there`, and the `.there`-shifted lookup on the
    extended valuation is definitionally the original lookup. Used by the
    `RLimbStore` arm, whose first emitted `varBind` (the literal word) lands in
    an anonymous temp. -/
theorem consistentS_weaken {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (x : ⟦t⟧) :
    ConsistentS vm.weaken (V.extend x) env := by
  intro s
  rw [← hc s]
  simp only [VarMap.weaken]
  cases hl : vm.lookup s with
  | none => rfl
  | some p => obtain ⟨t', v⟩ := p; rfl

/-! ## 2b. Fresh-temp namespace: `tmpName` injectivity + the env word-reader

The `RScalarSetExpr` front lowers an `SExpr` into a chain of `varBind`s over
FRESH temporaries `tmpName k = "__sx" ++ toString k`. The `SExpr`-recursion
homomorphism (below) needs those temporaries to be *disjoint by index* — i.e.
`tmpName` injective — which reduces to `Nat.repr` injective. That is not in
`Mathlib`/core, so it is proved here via a decimal-digit left inverse
(`toDigits_val : dval (Nat.toDigits 10 n) = n`). -/

/-- Decimal value of a digit-char list, MSB first (the left inverse of
    `Nat.toDigits 10`). -/
def dval (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- `foldl` with a running accumulator: `acc` contributes `acc * 10 ^ len`. -/
theorem foldl_acc (ds : List Char) (acc : Nat) :
    ds.foldl (fun a c => a * 10 + (c.toNat - 48)) acc = acc * 10 ^ ds.length + dval ds := by
  induction ds generalizing acc with
  | nil => simp [dval]
  | cons c cs ih =>
      simp only [List.foldl_cons, List.length_cons, dval]
      rw [ih (acc * 10 + (c.toNat - 48)), ih (0 * 10 + (c.toNat - 48))]
      ring

theorem dval_cons (c : Char) (ds : List Char) :
    dval (c :: ds) = (c.toNat - 48) * 10 ^ ds.length + dval ds := by
  simp only [dval, List.foldl_cons]
  rw [foldl_acc]
  simp only [zero_mul, zero_add]
  rfl

theorem digitChar_val {n : Nat} (h : n < 10) : (Nat.digitChar n).toNat - 48 = n := by
  interval_cases n <;> decide

theorem toDigitsCore_val (fuel : Nat) :
    ∀ (n : Nat) (ds : List Char), n < 10 ^ fuel →
      dval (Nat.toDigitsCore 10 fuel n ds) = n * 10 ^ ds.length + dval ds := by
  induction fuel with
  | zero =>
      intro n ds h
      simp only [pow_zero, Nat.lt_one_iff] at h
      subst h
      simp [Nat.toDigitsCore, dval]
  | succ fuel ih =>
      intro n ds h
      simp only [Nat.toDigitsCore]
      by_cases hn' : n / 10 = 0
      · rw [if_pos hn']
        have hlt : n < 10 := by
          rcases Nat.lt_or_ge n 10 with h1 | h1
          · exact h1
          · exact absurd (Nat.div_eq_zero_iff.mp hn') (by omega)
        rw [dval_cons, digitChar_val (by omega : n % 10 < 10), Nat.mod_eq_of_lt hlt]
      · rw [if_neg hn']
        have hn10 : n / 10 < 10 ^ fuel := by rw [pow_succ] at h; omega
        rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) hn10, dval_cons,
          digitChar_val (by omega : n % 10 < 10)]
        simp only [List.length_cons]
        have hP : (n / 10 * 10 + n % 10) * 10 ^ ds.length = n * 10 ^ ds.length := by
          rw [(by omega : n / 10 * 10 + n % 10 = n)]
        rw [pow_succ]
        linear_combination hP

theorem toDigits_val (n : Nat) : dval (Nat.toDigits 10 n) = n := by
  unfold Nat.toDigits
  rw [toDigitsCore_val (n + 1) n [] (by
    calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ 2 ^ (n + 1) := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ 10 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _)]
  simp [dval]

theorem repr_injective : Function.Injective Nat.repr := by
  intro a b h
  unfold Nat.repr at h
  have hd : Nat.toDigits 10 a = Nat.toDigits 10 b := by
    have := congrArg String.toList h; simpa using this
  have := toDigits_val a
  rw [hd, toDigits_val b] at this
  omega

/-- Fresh temporary name at counter `k`, matching the front's `tmpName`. -/
theorem tmpName_injective : Function.Injective TranslateDialectDirectArms.tmpName := by
  intro a b h
  unfold TranslateDialectDirectArms.tmpName at h
  simp only [String.append_right_inj] at h
  exact repr_injective (by simpa [toString] using h)

/-- A name is a fresh SExpr-lowering temporary iff it is `tmpName k` for some
    index `k`. The reserved `__sx` namespace, tracked structurally (avoids
    `String.isPrefixOf` reasoning). Source `SExpr` variables are `¬ isTmpName`. -/
def isTmpName (s : String) : Prop := ∃ k, s = TranslateDialectDirectArms.tmpName k

theorem isTmpName_tmpName (k : Nat) : isTmpName (TranslateDialectDirectArms.tmpName k) :=
  ⟨k, rfl⟩

/-- A name whose first character is not `'_'` is not a fresh temporary: every
    `tmpName k` starts with `"__sx"`. -/
theorem notTmp_of_headNe {s : String} {c : Char} {t : List Char}
    (hs : s.toList = c :: t) (hc : c ≠ '_') : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hd := congrArg String.toList hk
  rw [TranslateDialectDirectArms.tmpName, String.toList_append, hs] at hd
  simp only [show "__sx".toList = ['_', '_', 's', 'x'] from rfl,
    List.cons_append, List.nil_append] at hd
  injection hd with h1 _
  exact hc h1

/-- A name shorter than the four-character prefix `"__sx"` is not a fresh
    temporary. -/
theorem notTmp_of_len (s : String) (hs : s.length < 4) : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [TranslateDialectDirectArms.tmpName, String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  omega

theorem notTmp_empty : ¬ isTmpName "" := notTmp_of_len "" (by decide)

/-- A name is head-clean when it is non-empty and its first character is not
    `'_'`. `tmpName k = "__sx" ++ toString k` starts with `'_'`, so a head-clean
    name is never a fresh temporary, and it stays head-clean under any suffix. -/
def HeadOk (s : String) : Prop := ∃ c t, s.toList = c :: t ∧ c ≠ '_'

theorem HeadOk.notTmp {s : String} (h : HeadOk s) : ¬ isTmpName s := by
  obtain ⟨c, t, hs, hc⟩ := h
  exact notTmp_of_headNe hs hc

theorem HeadOk.append {s : String} (h : HeadOk s) (u : String) : HeadOk (s ++ u) := by
  obtain ⟨c, t, hs, hc⟩ := h
  exact ⟨c, t ++ u.toList, by rw [String.toList_append, hs]; rfl, hc⟩

/-- Read a `.sword 64` word slot out of an `SEnvScalar` (default `0` for an
    unbound / mistyped name). The `SExpr` word evaluator `SExpr.evalBV` reads its
    `SVar` leaves through this. -/
def envReader (env : SEnvScalar) : String → BitVec 64 :=
  fun s => match env s with
    | some ⟨.sword 64, w⟩ => w
    | _ => 0

/-- Read a `.sword 64` word slot out of an `SEnvScalar` as an `Option` (the
    partial-lookup twin of `envReader`, `some` exactly when the name is bound at
    `.sword 64`). Mirrors the front's `lookupU64` at the env level. -/
def envReadU64 (env : SEnvScalar) (nm : String) : Option (BitVec 64) :=
  match env nm with
  | some ⟨.sword 64, w⟩ => some w
  | _ => none

/-- One binary node of the `SExpr` env-mirror: given the env *after* both
    operands are lowered and their result names `na`, `nb`, read both words and
    bind a fresh temp `tmpName cnt` to `f va vb` (the word `f` the front's emitted
    op denotes). `none` if either operand slot is not a `u64` word. -/
def binNode (envAB : SEnvScalar) (na nb : String) (cnt : Nat)
    (f : BitVec 64 → BitVec 64 → BitVec 64) : Option (SEnvScalar × String × Nat) :=
  match envReadU64 envAB na, envReadU64 envAB nb with
  | some va, some vb =>
      some (envAB.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64) (f va vb),
        TranslateDialectDirectArms.tmpName cnt, cnt + 1)
  | _, _ => none

/-- **Env-level image of `lowerSExpr`.** The scalar-word twin of the SIMD `semV`
    fold: mirrors the front's fresh-temp chain at the `SEnvScalar` level, binding
    each node's fresh temp to the SAME word the front's emitted `catCryptDialect`
    op denotes (`bvConst`/`bvAdd`/… — front-faithful, so the preservation
    homomorphism `translateDialectFull_denote` ties them via `ConsistentS` with NO
    freshness reasoning). The shift arms use `SExpr.evalBV`'s uniform
    variable-amount convention (`va <<< vb.toNat` / `va >>> vb.toNat`); when the
    amount is a literal `SLit k` the front instead emits the immediate op
    `bvShiftL 64 k` / `bvShiftR 64 k`, and the two agree exactly under
    `srcClean`'s `k < 2^64` literal bound (`(BitVec.ofNat 64 k).toNat = k`).
    Declines exactly the arms `lowerSExpr` declines. -/
def semLowerSExpr (env : SEnvScalar) (cnt : Nat) : SExpr → Option (SEnvScalar × String × Nat)
  | .SVar x =>
      match envReadU64 env x with
      | some _ => some (env, x, cnt)
      | none => none
  | .SLit n =>
      some (env.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64) (BitVec.ofNat 64 n),
        TranslateDialectDirectArms.tmpName cnt, cnt + 1)
  | .SAdd a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (· + ·)
          | none => none
      | none => none
  | .SSub a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (· - ·)
          | none => none
      | none => none
  | .SMul a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (· * ·)
          | none => none
      | none => none
  | .SAnd a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (· &&& ·)
          | none => none
      | none => none
  | .SXor a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (· ^^^ ·)
          | none => none
      | none => none
  | .SShl a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (fun va vb => va <<< vb.toNat)
          | none => none
      | none => none
  | .SShr a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) => binNode e2 na nb c2 (fun va vb => va >>> vb.toNat)
          | none => none
      | none => none
  | .SMulHiU a b =>
      match semLowerSExpr env cnt a with
      | some (e1, na, c1) =>
          match semLowerSExpr e1 c1 b with
          | some (e2, nb, c2) =>
              binNode e2 na nb c2 (fun va vb => VIR.CatCryptDialect.mulHiC va vb)
          | none => none
      | none => none
  | _ => none

/-- Source-cleanliness of an `SExpr`: its `SVar`/`SLimb` variables are NOT in the
    reserved `__sx` temp namespace (so the front's fresh temporaries never collide
    with a source read), and its `SLit` literals are `< 2^64` (so a literal shift
    amount `k` reconciles with `SExpr.evalBV`'s `(BitVec.ofNat 64 k).toNat`). Real
    kernels (index arithmetic over named slots, small shift constants) satisfy it. -/
def srcClean : SExpr → Prop
  | .SVar x => ¬ isTmpName x
  | .SLit n => n < 2 ^ 64
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => srcClean a ∧ srcClean b
  | _ => False

/-! ## 3. Scalar operational semantics of the covered straight-line arms -/

/-- The env-level fold behind the `RCallN` multi-dest leaf call: bind each
    destination in turn to the opaque `CryptoTy.default` waist (the dialect
    `extCall` denotation). Mirrors `loopCallNDestsD`'s left-to-right recursion
    (process the head dest, recurse on the tail against the updated env), so the
    `RCallN` induction case closes by structural recursion on `dests`. -/
def semCallNDests : List Located → SEnvScalar → SEnvScalar
  | [], env => env
  | d :: rest, env =>
      semCallNDests rest
        (env.upd d.locVar (t := encodeTy d.locDst) (CryptoTy.default (encodeTy d.locDst)))

/-- The φ-merge select: the word value the front's six-op `RIfNz` (C′) merge
    chain computes — `zero → else`, `nonzero → then` (the `ite (not (bvEq cond
    zero))` cmov). Stated over a literal `BitVec w` parameter so the `Decidable`
    instance on the guard is found without unfolding `⟦.sword w⟧`. -/
def phiSelect {w : Nat} (condv : BitVec w) (thenV elseV : BitVec 64) : BitVec 64 :=
  if condv = 0#w then elseV else thenV

/-- The φ-merge zero test (the `bvEq cond zero` bit), over a literal `BitVec w`
    parameter for the same `Decidable`-resolution reason as `phiSelect`. -/
def condIsZero {w : Nat} (v : BitVec w) : Bool := decide (v = 0#w)

/-- The constant-time word select `RSelect` computes: the first source when the
    selector is zero, the second otherwise (`RustExec.selectFalse` /
    `RustExec.selectTrue`). -/
def selectWord (s a c : BitVec 64) : BitVec 64 :=
  if s = 0#64 then a else c

/-- The env-level fold behind the bounded `RFor` loop: run the body semantics
    once per trip, binding the counter `x` to the trip index `n` (ascending
    `0, 1, …, N-1`), peeling the LAST trip first — the exact recursion shape of
    the front's meta-unroll `loopRForD`, so the `RFor` induction case closes by
    `Nat`-induction in lock-step. The body semantics `semBody` is passed in
    (as `loopRForD` takes `translateBody`), so this def can be stated before
    `semScalar`'s `RFor` arm is in scope. -/
def semRForD (semBody : SEnvScalar → Option SEnvScalar) (x : String) :
    Nat → SEnvScalar → Option SEnvScalar
  | 0, env => some env
  | n + 1, env =>
      match semRForD semBody x n env with
      | some envPre => semBody (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n))
      | none => none

/-- Pure operational semantics of the covered scalar `LowCT` arms as a partial
    `SEnvScalar` transformer. Each arm binds its destination to the SAME waist the
    front's emitted `catCryptDialect` op denotes by:

    * `RCall` — an opaque leaf: `CryptoTy.default (encodeTy dst)` (the dialect
      `extCall` denotation, independent of the argument values);
    * `RSelect` — `selectWord s a c` on 64-bit word slots, the value of the
      front's mask chain; on any other slots the opaque `extCall "select"`
      default;
    * `RArrLoadLit` / `RArrStoreLit` — the read `memGetDyn arr i` / write
      `memSetDyn arr i v` at the literal index `i` taken as a 64-bit word, when the
      array has tower type `TArr _ .TU64` and is bound as a `.memref n`, and the
      destination (load) or source (store) is a 64-bit word; else the opaque
      default, byte and `u32` arrays included;
    * `RArrLoad` — the dynamic-index read `memGetDyn arr i` when the array slot is
      a `.memref n`, the index a `.sword 64`, and the destination a `u64` word;
      else the opaque `extCall "arrLoadDyn"` default;
    * `RArrStore` — the dynamic-index write `memSetDyn arr i v` when the shapes
      line up and the destination array's encoding is `.memref n`; else the opaque
      default. -/
def semScalar : LowCT → SEnvScalar → Option SEnvScalar
  | .RSkip, env => some env
  | .RBlock body, env => semScalar body env
  -- `RAssert label` names a proposition in the proof context and reads no
  -- operand; `RustExec.assert` leaves the state unchanged, so the waist is the
  -- identity on the env — the same waist the front's empty emission denotes by.
  | .RAssert _label, env => some env
  | .RSeq c₁ c₂, env => (semScalar c₁ env).bind (fun e => semScalar c₂ e)
  | .RScalarSet name n, env =>
      some (env.upd name (t := .sword 64) (BitVec.ofNat 64 n))
  | .RLetU64Zero name body, env =>
      semScalar body (env.upd name (t := .sword 64) (0 : BitVec 64))
  -- `RLetZero` declares a tower slot the body writes before it reads; the front
  -- emits nothing for it, and the waist is the body's on the unchanged env.
  | .RLetZero _name _tt body, env => semScalar body env
  | .RCall _fname dst _args, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy) (CryptoTy.default retTy))
  | .RSelect dst sel src0 src1, env =>
      match dst.locDst, env sel, env src0.locVar, env src1.locVar with
      | .TU64, some ⟨.sword 64, s⟩, some ⟨.sword 64, a⟩, some ⟨.sword 64, c⟩ =>
          some (env.upd dst.locVar (t := .sword 64) (selectWord s a c))
      | _, _, _, _ =>
          let retTy := encodeTy dst.locDst
          some (env.upd dst.locVar (t := retTy) (CryptoTy.default retTy))
  | .RCallDstThreaded _fname dst _args, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy) (CryptoTy.default retTy))
  | .RTupleLoad dst _src _idx, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy) (CryptoTy.default retTy))
  | .RArrLoadLit dst src idx, env =>
      match dst.locDst, src.locDst, env src.locVar with
      | .TU64, .TArr _ .TU64, some ⟨.memref _n, arr⟩ =>
          some (env.upd dst.locVar (t := .sword 64)
            (memGetDyn arr (BitVec.ofNat 64 idx).toNat))
      | _, _, _ =>
          let retTy := encodeTy dst.locDst
          some (env.upd dst.locVar (t := retTy) (CryptoTy.default retTy))
  | .RArrStoreLit arr idx src, env =>
      match arr.locDst, env arr.locVar, env src.locVar with
      | .TArr _ .TU64, some ⟨.memref n, a⟩, some ⟨.sword 64, v⟩ =>
          some (env.upd arr.locVar (t := .memref n)
            (memSetDyn a (BitVec.ofNat 64 idx).toNat v))
      | _, _, _ =>
          let retTy := encodeTy arr.locDst
          some (env.upd arr.locVar (t := retTy) (CryptoTy.default retTy))
  | .RCallSwap _fname dest1 dest2 _args, env =>
      let retTy1 := encodeTy dest1.locDst
      let retTy2 := encodeTy dest2.locDst
      some ((env.upd dest1.locVar (t := retTy1) (CryptoTy.default retTy1)).upd
        dest2.locVar (t := retTy2) (CryptoTy.default retTy2))
  | .RCloneCall cv _tt oldDest _innerF newDest _args, env =>
      match env oldDest.locVar with
      | some ⟨cloneTy, _⟩ =>
          let retTy := encodeTy newDest.locDst
          some ((env.upd cv (t := cloneTy) (CryptoTy.default cloneTy)).upd
            newDest.locVar (t := retTy) (CryptoTy.default retTy))
      | none => none
  | .RLimbStore loc idx v, env =>
      match env loc.locVar with
      | some ⟨.memref n, arr⟩ =>
          if h : idx < n then
            some (env.upd loc.locVar (t := .memref n)
              (fun j => if j = ⟨idx, h⟩ then v else arr j))
          else none
      | none =>
          match encodeTy loc.locDst with
          | .memref n =>
              if idx < n then
                some (env.upd loc.locVar (t := .memref n) (CryptoTy.default (.memref n)))
              else none
          | _ => none
      | some _ => none
  | .RCallN _fname dests _args, env => some (semCallNDests dests env)
  | .RArrLoad dst src idxVar, env =>
      match dst.locDst, env src.locVar, env idxVar with
      | .TU64, some ⟨.memref _n, arr⟩, some ⟨.sword 64, i⟩ =>
          some (env.upd dst.locVar (t := .sword 64) (memGetDyn arr i.toNat))
      | dty, _, _ =>
          some (env.upd dst.locVar (t := encodeTy dty) (CryptoTy.default (encodeTy dty)))
  | .RArrStore arr idxVar src, env =>
      let dty := arr.locDst
      match env arr.locVar, env idxVar, env src.locVar with
      | some ⟨.memref n, a⟩, some ⟨.sword 64, i⟩, some ⟨.sword 64, v⟩ =>
          if h : encodeTy dty = .memref n then
            some (env.upd arr.locVar (t := encodeTy dty)
              (h.symm ▸ (memSetDyn a i.toNat v)))
          else
            some (env.upd arr.locVar (t := encodeTy dty) (CryptoTy.default (encodeTy dty)))
      | _, _, _ =>
          some (env.upd arr.locVar (t := encodeTy dty) (CryptoTy.default (encodeTy dty)))
  | .RScalarSetExpr x e, env =>
      match semLowerSExpr env 0 e with
      | some (env2, _nm, _) =>
          some (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e))
      | none => none
  | .RFor x N body, env => semRForD (fun e => semScalar body e) x N env
  | .RIfNz name thenBr elseBr, env =>
      -- The waist the front's `RIfNz` lowering denotes by (the exact mirror of
      -- `translateDialectControl`'s case analysis): the guard must be a bound
      -- scalar; when both branches are a single `RScalarSet` on the SAME name —
      -- the (C′) φ-merge, the only case the front compiles as a
      -- conditional — bind that name to the cmov-selected value (`zero → else`,
      -- `nonzero → then`); every other case composes the branch semantics
      -- sequentially (`then; else`), which is what the front's pass-through /
      -- re-translation cases (A)/(B)/(C-otherwise) emit — in (A)/(B) the front
      -- passes through ONE branch's prefix, and the discarded branch is
      -- context-invariant hence env-inert (`translateDialectControl_ext`), so
      -- the sequential composition is denotation-equal there.
      match env name with
      | some ⟨.sword w, condv⟩ =>
          match asSingleScalarSet thenBr, asSingleScalarSet elseBr with
          | some thenSet, some elseSet =>
              if thenSet.name = elseSet.name then
                some (env.upd thenSet.name (t := .sword 64)
                  (phiSelect (w := w) condv (BitVec.ofNat 64 thenSet.val)
                    (BitVec.ofNat 64 elseSet.val)))
              else
                (semScalar thenBr env).bind (fun e => semScalar elseBr e)
          | _, _ => (semScalar thenBr env).bind (fun e => semScalar elseBr e)
      | _ => none
  | _, _ => none

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## 3b. The waist semantics at a leaf oracle

`semScalarL ls` is `semScalar` with the destination of every opaque leaf call bound to
the value of the leaf oracle `ls` at the leaf name, the destination type and the
argument values read from the environment (`argVals`). The table of leaf names and
arguments per arm is in `Dialects.LeafOracleScalar`. At the default oracle it is
`semScalar` (`semScalarL_default`). -/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr callNLeafName)

/-- The typed values the environment binds at the given names, unbound names dropped. -/
def argVals (env : SEnvScalar) (names : List String) : List ((t : CryptoTy) × ⟦t⟧) :=
  names.filterMap env

/-- The variable names of a list of located arguments. -/
def locNames (xs : List Located) : List String := xs.map (·.locVar)

/-- The `RCallN` fold at a leaf oracle: destination `i` is bound to the oracle at
    `callNLeafName fname i`, the arguments read from the environment before the
    write. -/
def semCallNDestsL (ls : SemLeafSpec) (fname : String) (args : List Located) :
    List Located → Nat → SEnvScalar → SEnvScalar
  | [], _, env => env
  | d :: rest, i, env =>
      semCallNDestsL ls fname args rest (i + 1)
        (env.upd d.locVar (t := encodeTy d.locDst)
          (ls (callNLeafName fname i) (encodeTy d.locDst) (argVals env (locNames args))))

/-- The waist semantics of `semScalar`, with each opaque leaf call bound to the value of
    the leaf oracle `ls` instead of `CryptoTy.default`. The non-leaf arms are those of
    `semScalar`. -/
def semScalarL (ls : SemLeafSpec) : LowCT → SEnvScalar → Option SEnvScalar
  | .RSkip, env => some env
  | .RBlock body, env => semScalarL ls body env
  | .RAssert _label, env => some env
  | .RSeq c₁ c₂, env => (semScalarL ls c₁ env).bind (fun e => semScalarL ls c₂ e)
  | .RScalarSet name n, env =>
      some (env.upd name (t := .sword 64) (BitVec.ofNat 64 n))
  | .RLetU64Zero name body, env =>
      semScalarL ls body (env.upd name (t := .sword 64) (0 : BitVec 64))
  | .RLetZero _name _tt body, env => semScalarL ls body env
  | .RCall fname dst args, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy) (ls fname retTy (argVals env (locNames args))))
  | .RSelect dst sel src0 src1, env =>
      match dst.locDst, env sel, env src0.locVar, env src1.locVar with
      | .TU64, some ⟨.sword 64, s⟩, some ⟨.sword 64, a⟩, some ⟨.sword 64, c⟩ =>
          some (env.upd dst.locVar (t := .sword 64) (selectWord s a c))
      | _, _, _, _ =>
          let retTy := encodeTy dst.locDst
          some (env.upd dst.locVar (t := retTy)
            (ls "select" retTy (argVals env (sel :: locNames [src0, src1]))))
  | .RCallDstThreaded fname dst args, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy)
        (ls fname retTy (argVals env (locNames (dst :: args)))))
  | .RTupleLoad dst src idx, env =>
      let retTy := encodeTy dst.locDst
      some (env.upd dst.locVar (t := retTy)
        (ls ("tupleLoad:" ++ toString idx) retTy (argVals env (locNames [src]))))
  | .RArrLoadLit dst src idx, env =>
      match dst.locDst, src.locDst, env src.locVar with
      | .TU64, .TArr _ .TU64, some ⟨.memref _n, arr⟩ =>
          some (env.upd dst.locVar (t := .sword 64)
            (memGetDyn arr (BitVec.ofNat 64 idx).toNat))
      | _, _, _ =>
          let retTy := encodeTy dst.locDst
          some (env.upd dst.locVar (t := retTy)
            (ls ("arrLoad:" ++ toString idx) retTy (argVals env (locNames [src]))))
  | .RArrStoreLit arr idx src, env =>
      match arr.locDst, env arr.locVar, env src.locVar with
      | .TArr _ .TU64, some ⟨.memref n, a⟩, some ⟨.sword 64, v⟩ =>
          some (env.upd arr.locVar (t := .memref n)
            (memSetDyn a (BitVec.ofNat 64 idx).toNat v))
      | _, _, _ =>
          let retTy := encodeTy arr.locDst
          some (env.upd arr.locVar (t := retTy)
            (ls ("arrStore:" ++ toString idx) retTy (argVals env (locNames [arr, src]))))
  | .RCallSwap fname dest1 dest2 args, env =>
      let retTy1 := encodeTy dest1.locDst
      let retTy2 := encodeTy dest2.locDst
      let env1 := env.upd dest1.locVar (t := retTy1)
        (ls fname retTy1 (argVals env (locNames args)))
      some (env1.upd dest2.locVar (t := retTy2) (ls fname retTy2 (argVals env1 (locNames args))))
  | .RCloneCall cv _tt oldDest innerF newDest args, env =>
      match env oldDest.locVar with
      | some ⟨cloneTy, old⟩ =>
          let retTy := encodeTy newDest.locDst
          let env1 := env.upd cv (t := cloneTy) (ls "clone" cloneTy [⟨cloneTy, old⟩])
          some (env1.upd newDest.locVar (t := retTy)
            (ls innerF retTy (argVals env1 (locNames args))))
      | none => none
  | .RLimbStore loc idx v, env =>
      match env loc.locVar with
      | some ⟨.memref n, arr⟩ =>
          if h : idx < n then
            some (env.upd loc.locVar (t := .memref n)
              (fun j => if j = ⟨idx, h⟩ then v else arr j))
          else none
      | none =>
          match encodeTy loc.locDst with
          | .memref n =>
              if idx < n then
                some (env.upd loc.locVar (t := .memref n)
                  (ls (TranslateDialectDirectArms.limbLitLeafName idx) (.memref n)
                    [⟨.sword 64, v⟩]))
              else none
          | _ => none
      | some _ => none
  | .RCallN fname dests args, env => some (semCallNDestsL ls fname args dests 0 env)
  | .RArrLoad dst src idxVar, env =>
      match dst.locDst, env src.locVar, env idxVar with
      | .TU64, some ⟨.memref _n, arr⟩, some ⟨.sword 64, i⟩ =>
          some (env.upd dst.locVar (t := .sword 64) (memGetDyn arr i.toNat))
      | dty, _, _ =>
          some (env.upd dst.locVar (t := encodeTy dty)
            (ls "arrLoadDyn" (encodeTy dty) (argVals env (locNames [src] ++ [idxVar]))))
  | .RArrStore arr idxVar src, env =>
      let dty := arr.locDst
      match env arr.locVar, env idxVar, env src.locVar with
      | some ⟨.memref n, a⟩, some ⟨.sword 64, i⟩, some ⟨.sword 64, v⟩ =>
          if h : encodeTy dty = .memref n then
            some (env.upd arr.locVar (t := encodeTy dty)
              (h.symm ▸ (memSetDyn a i.toNat v)))
          else
            some (env.upd arr.locVar (t := encodeTy dty)
              (ls "arrStoreDyn" (encodeTy dty) (argVals env (locNames [arr, src] ++ [idxVar]))))
      | _, _, _ =>
          some (env.upd arr.locVar (t := encodeTy dty)
            (ls "arrStoreDyn" (encodeTy dty) (argVals env (locNames [arr, src] ++ [idxVar]))))
  | .RScalarSetExpr x e, env =>
      match semLowerSExpr env 0 e with
      | some (env2, _nm, _) =>
          some (env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e))
      | none => none
  | .RFor x N body, env => semRForD (fun e => semScalarL ls body e) x N env
  | .RIfNz name thenBr elseBr, env =>
      match env name with
      | some ⟨.sword w, condv⟩ =>
          match asSingleScalarSet thenBr, asSingleScalarSet elseBr with
          | some thenSet, some elseSet =>
              if thenSet.name = elseSet.name then
                some (env.upd thenSet.name (t := .sword 64)
                  (phiSelect (w := w) condv (BitVec.ofNat 64 thenSet.val)
                    (BitVec.ofNat 64 elseSet.val)))
              else
                (semScalarL ls thenBr env).bind (fun e => semScalarL ls elseBr e)
          | _, _ => (semScalarL ls thenBr env).bind (fun e => semScalarL ls elseBr e)
      | _ => none
  | _, _ => none

/-- At the default oracle the `RCallN` fold is `semCallNDests`. -/
theorem semCallNDestsL_default (fname : String) (args : List Located) :
    ∀ (dests : List Located) (i : Nat) (env : SEnvScalar),
      semCallNDestsL defaultLeaf fname args dests i env = semCallNDests dests env
  | [], _, _ => rfl
  | _ :: rest, i, _ => semCallNDestsL_default fname args rest (i + 1) _

/-- `semScalarL` on a `RLetZero` binder is `semScalarL` of its body. -/
theorem semScalarL_rLetZero (ls : SemLeafSpec) (name : String) (tt : TowerType)
    (body : LowCT) (env : SEnvScalar) :
    semScalarL ls (.RLetZero name tt body) env = semScalarL ls body env := rfl

/-- `semScalar` on a `RLetZero` binder is `semScalar` of its body. -/
theorem semScalar_rLetZero (name : String) (tt : TowerType) (body : LowCT)
    (env : SEnvScalar) :
    semScalar (.RLetZero name tt body) env = semScalar body env := rfl

/-- At the default oracle `semScalarL` is `semScalar`. -/
theorem semScalarL_default : ∀ (c : LowCT) (env : SEnvScalar),
    semScalarL defaultLeaf c env = semScalar c env := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => intro env; simp only [semScalarL, semScalar, ih₁, ih₂]
  | RBlock body ih => intro env; simp only [semScalarL, semScalar, ih]
  | RLetU64Zero name body ih => intro env; simp only [semScalarL, semScalar, ih]
  | RLetZero name tt body ih => intro env; rw [semScalarL_rLetZero, semScalar_rLetZero, ih]
  | RFor x N body ih => intro env; simp only [semScalarL, semScalar, ih]
  | RIfNz name thenBr elseBr ihT ihE =>
      intro env; simp only [semScalarL, semScalar, ihT, ihE]
  | RCallN fname dests args =>
      intro env; simp only [semScalarL, semScalar, semCallNDestsL_default]
  | _ => intro env; rfl

/-- `semScalar` is `semScalarL` at the default oracle. -/
theorem semScalar_eq_semScalarL : semScalar = semScalarL defaultLeaf := by
  funext c env; exact (semScalarL_default c env).symm

end CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr callNLeafName)

/-! ## 4. The straight-line covered fragment

`IsCoveredS` marks the straight-line scalar arms this preservation theorem
covers: the leaf-call arm (`RCall`), the dynamic-index array **load**/**store**
arms (`RArrLoad` / `RArrStore`), plus their `RSeq` / `RBlock` / `RSkip` closure.
Deliberately separate from `IsCoveredCtl` (same shape, fewer arms). The
scalar-`SExpr` assignment (`RScalarSetExpr x e`, with `srcClean e`) is
covered via the `SExpr`-recursion homomorphism `lowerSExpr_denote` (§5f, §7); its
constructor carries the `srcClean` side condition (`SExpr` over the arithmetic /
bitwise / shift / high-multiply fragment, non-`__sx` source variables). The
contract assertion `RAssert` is covered with no side condition (§4b). The
control arms `RFor` / `RIfNz` are covered by the Stage-2 extension
`IsCoveredSCtl` (§8), which reaches `RAssert` through `ofStraight`. -/

/-- The straight-line scalar-covered `LowCT` fragment. -/
inductive IsCoveredS : LowCT → Prop
  | rSkip : IsCoveredS .RSkip
  | rBlock {body : LowCT} : IsCoveredS body → IsCoveredS (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsCoveredS c₁ → IsCoveredS c₂ → IsCoveredS (.RSeq c₁ c₂)
  | rScalarSet (name : String) (n : Nat) : IsCoveredS (.RScalarSet name n)
  | rLetU64Zero {name : String} {body : LowCT} :
      IsCoveredS body → IsCoveredS (.RLetU64Zero name body)
  | rCall (fname : String) (dst : Located) (args : List Located) :
      IsCoveredS (.RCall fname dst args)
  | rSelect (dst : Located) (sel : String) (src0 src1 : Located) :
      IsCoveredS (.RSelect dst sel src0 src1)
  | rCallDstThreaded (fname : String) (dst : Located) (args : List Located) :
      IsCoveredS (.RCallDstThreaded fname dst args)
  | rTupleLoad (dst src : Located) (idx : Nat) :
      IsCoveredS (.RTupleLoad dst src idx)
  | rArrLoadLit (dst src : Located) (idx : Nat) :
      IsCoveredS (.RArrLoadLit dst src idx)
  | rArrStoreLit (arr : Located) (idx : Nat) (src : Located) :
      IsCoveredS (.RArrStoreLit arr idx src)
  | rCallSwap (fname : String) (dest1 dest2 : Located) (args : List Located) :
      IsCoveredS (.RCallSwap fname dest1 dest2 args)
  | rCloneCall (cv : String) (tt : TowerType) (oldDest : Located) (innerF : String)
      (newDest : Located) (args : List Located) :
      IsCoveredS (.RCloneCall cv tt oldDest innerF newDest args)
  | rLimbStore (loc : Located) (idx : Nat) (v : BitVec 64) :
      IsCoveredS (.RLimbStore loc idx v)
  | rCallN (fname : String) (dests args : List Located) :
      IsCoveredS (.RCallN fname dests args)
  | rArrLoad (dst src : Located) (idxVar : String) :
      IsCoveredS (.RArrLoad dst src idxVar)
  | rArrStore (arr : Located) (idxVar : String) (src : Located) :
      IsCoveredS (.RArrStore arr idxVar src)
  | rScalarSetExpr (x : String) (e : SExpr) (hclean : srcClean e) :
      IsCoveredS (.RScalarSetExpr x e)
  | rAssert (label : String) : IsCoveredS (.RAssert label)

/-- `IsCoveredS` refines the front-simulation coverage `IsCovered`: the arms
    are 1:1, with `rScalarSetExpr` forgetting the `srcClean` side condition.
    Lets one `IsCoveredS` hypothesis feed both the preservation homomorphism
    (here) and the operational simulation (`rustExecSimulatesDialect`). -/
theorem IsCoveredS.toIsCovered {c : LowCT} (h : IsCoveredS c) : IsCovered c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rScalarSet name n => exact .rScalarSet name n
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rCall fname dst args => exact .rCall fname dst args
  | rSelect dst sel src0 src1 => exact .rSelect dst sel src0 src1
  | rCallDstThreaded fname dst args => exact .rCallDstThreaded fname dst args
  | rTupleLoad dst src idx => exact .rTupleLoad dst src idx
  | rArrLoadLit dst src idx => exact .rArrLoadLit dst src idx
  | rArrStoreLit arr idx src => exact .rArrStoreLit arr idx src
  | rCallSwap fname dest1 dest2 args => exact .rCallSwap fname dest1 dest2 args
  | rCloneCall cv tt oldDest innerF newDest args =>
      exact .rCloneCall cv tt oldDest innerF newDest args
  | rLimbStore loc idx v => exact .rLimbStore loc idx v
  | rCallN fname dests args => exact .rCallN fname dests args
  | rArrLoad dst src idxVar => exact .rArrLoad dst src idxVar
  | rArrStore arr idxVar src => exact .rArrStore arr idxVar src
  | rScalarSetExpr x e _ => exact .rScalarSetExpr x e
  | rAssert label => exact .rAssert label

/-! ### 4b. Assertion erasure

`RAssert label` carries a proof-context label and no operand: no value is read,
so the front emits nothing (`translateDialectFull_rAssert_seq`) and the waist
semantics steps the env by the identity. The two erasure statements are the
correctness obligation for dropping an assertion — the emitted program and the
`semScalar` result of a sequence are both independent of an assertion in front
of it. Because the constructor holds no expression, the arm carries no
publicness side condition: there is no operand whose secrecy could make the
dropped check a branch on a secret (`LowCT.cmdCT` accepts `RAssert`
unconditionally, and its `LowCTLeakTraceDef` leak trace is empty). -/

/-- The waist semantics of a sequence is unchanged by an assertion in front. -/
theorem semScalar_rAssert_seq (label : String) (c : LowCT) (env : SEnvScalar) :
    semScalar (.RSeq (.RAssert label) c) env = semScalar c env := by
  simp [semScalar]

/-- The waist semantics of a select whose destination is a `u64` word and whose
    selector and sources hold 64-bit words binds the destination to `selectWord`. -/
theorem semScalar_rSelect_word (dst : Located) (sel : String) (src0 src1 : Located)
    (env : SEnvScalar) (s a c : BitVec 64) (hd : dst.locSrc = .TU64)
    (hs : env sel = some ⟨.sword 64, s⟩) (ha : env src0.locVar = some ⟨.sword 64, a⟩)
    (hc : env src1.locVar = some ⟨.sword 64, c⟩) :
    semScalar (.RSelect dst sel src0 src1) env =
      some (env.upd dst.locVar (t := .sword 64) (selectWord s a c)) := by
  simp only [semScalar, Located.locDst, hd, hs, ha, hc]

/-- The waist semantics of a literal-index read of a `u64` word array
    (`TArr k .TU64`) into a `u64` word. -/
theorem semScalar_rArrLoadLit_word (dst src : Located) (idx : Nat) (env : SEnvScalar)
    (k n : Nat) (arr : Fin n → BitVec 64) (hd : dst.locSrc = .TU64)
    (hsrc : src.locSrc = .TArr k .TU64)
    (hs : env src.locVar = some ⟨.memref n, arr⟩) :
    semScalar (.RArrLoadLit dst src idx) env =
      some (env.upd dst.locVar (t := .sword 64) (memGetDyn arr (BitVec.ofNat 64 idx).toNat)) := by
  simp only [semScalar, Located.locDst, hd, hsrc, hs]

/-- The waist semantics of a literal-index write of a word into a `u64` word array
    (`TArr k .TU64`). -/
theorem semScalar_rArrStoreLit_word (arr src : Located) (idx : Nat) (env : SEnvScalar)
    (k n : Nat) (a : Fin n → BitVec 64) (v : BitVec 64)
    (harr : arr.locSrc = .TArr k .TU64)
    (ha : env arr.locVar = some ⟨.memref n, a⟩) (hs : env src.locVar = some ⟨.sword 64, v⟩) :
    semScalar (.RArrStoreLit arr idx src) env =
      some (env.upd arr.locVar (t := .memref n) (memSetDyn a (BitVec.ofNat 64 idx).toNat v)) := by
  simp only [semScalar, Located.locDst, harr, ha, hs]

/-! ## 5. Op-denotation helpers (the waist each single-binding arm binds by) -/

/-- An opaque `extCall` denotes to `CryptoTy.default retTy`, independent of its
    arguments (the dialect compile-path meaning of an opaque leaf). -/
theorem extCallExpr_denote {Γ : Ctx} (name : String) (retTy : CryptoTy)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    (extCallExpr name retTy hv).denote V = CryptoTy.default retTy := rfl

/-- At the leaf oracle `ls`, an opaque `extCall` denotes to `ls` at its name, return
    type and looked-up argument values. -/
theorem extCallExpr_denoteWith (ls : SemLeafSpec) {Γ : Ctx} (name : String)
    (retTy : CryptoTy) {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    @Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ (extCallExpr name retTy hv) V
      = ls name retTy (hvecSigmaList (Expr.lookupArgs (toVIRArgs hv) V)) := rfl

/-- The argument values of a resolved argument vector, looked up in `V`, are the
    resolved variables looked up one by one. -/
theorem hvecSigmaList_listSigma {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∀ (ra : List ((t : CryptoTy) × CVar Γ t)),
      hvecSigmaList (Expr.lookupArgs (toVIRArgs (listSigmaToCHVector ra).snd) V)
        = ra.map (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))
  | [] => rfl
  | ⟨t, v⟩ :: rest => by
      have ih := hvecSigmaList_listSigma V rest
      simp only [listSigmaToCHVector]
      rcases hl : listSigmaToCHVector rest with ⟨ts, hv⟩
      rw [hl] at ih
      simp only [List.map_cons]
      rw [← ih]
      rfl

/-- Under `ConsistentS vm V env`, the values of the arguments `args` resolved through
    `vm` and looked up in `V` are the values `argVals` reads from `env`. -/
theorem argVals_of_resolve {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) :
    ∀ (args : List Located) (ra : List ((t : CryptoTy) × CVar Γ t)),
      resolveLocatedArgs vm args = some ra →
      hvecSigmaList (Expr.lookupArgs (toVIRArgs (listSigmaToCHVector ra).snd) V)
        = argVals env (locNames args) := by
  intro args ra hra
  rw [hvecSigmaList_listSigma]
  induction args generalizing ra with
  | nil =>
      simp only [resolveLocatedArgs, Option.some.injEq] at hra
      subst hra; rfl
  | cons a rest ih =>
      simp only [resolveLocatedArgs] at hra
      rcases hl : vm.lookup a.locVar with _ | r
      · simp [hl] at hra
      · rcases hr : resolveLocatedArgs vm rest with _ | rs
        · simp [hl, hr] at hra
        · simp only [hl, hr, Option.some.injEq] at hra
          subst hra
          have ha : env a.locVar = some ⟨r.1, (toVIRVar r.2).lookup V⟩ := by
            rw [← hc a.locVar, hl]; rfl
          simp only [List.map_cons, argVals, locNames, List.filterMap_cons, ha]
          congr 1
          exact ih rs hr

/-- The `memrefGetDyn` expression denotes to the dynamic-index read `memGetDyn`. -/
theorem memrefGetDyn_denote {Γ : Ctx} (n : Nat) (arrV : CVar Γ (.memref n))
    (idxV : CVar Γ (.sword 64)) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    (Expr.denote (d := catCryptDialect)
      { op := .memrefGetDyn n, retTy_eq := rfl,
        args := .cons (toVIRVar arrV) (.cons (toVIRVar idxV) .nil) } V)
      = memGetDyn ((toVIRVar arrV).lookup V) ((toVIRVar idxV).lookup V).toNat := rfl

/-- The `memrefSetDyn` expression denotes to the dynamic-index write `memSetDyn`. -/
theorem memrefSetDyn_denote {Γ : Ctx} (n : Nat) (arrV : CVar Γ (.memref n))
    (idxV srcV : CVar Γ (.sword 64)) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    (Expr.denote (d := catCryptDialect)
      { op := .memrefSetDyn n, retTy_eq := rfl,
        args := .cons (toVIRVar arrV)
          (.cons (toVIRVar idxV) (.cons (toVIRVar srcV) .nil)) } V)
      = memSetDyn ((toVIRVar arrV).lookup V) ((toVIRVar idxV).lookup V).toNat
          ((toVIRVar srcV).lookup V) := rfl

/-! ## 5b. `varBind`-factoring of the array combinators

Both branches of `arrLoadCont` are a single `ComCont.varBind`; `arrLoadExpr`
extracts the bound expression (`memrefGetDyn` on the real dynamic-index ABI,
else the opaque `extCall "arrLoadDyn"`). Factoring the combinator as
`ComCont.varBind (arrLoadExpr …)` lets the `RArrLoad` induction case close by
`scalar_step` exactly as `RCall` does — the two front-emitted matches
(`arrLoadExpr` and `semScalar`'s `RArrLoad` arm) are driven in lock-step by a
double `split` (the diagonal cases agree by the §5 denotation lemmas; the cross
cases are discriminant-contradictory). -/

/-- The single expression `arrLoadCont` binds, in both branches. -/
def arrLoadExpr {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    Expr catCryptDialect Γ (encodeTy dty) :=
  match dty, resolvedArgs, idxSig with
  | .TU64, [⟨.memref n, arrV⟩], ⟨.sword 64, idxV⟩ =>
      { op := .memrefGetDyn n, retTy_eq := rfl,
        args := .cons (toVIRVar arrV) (.cons (toVIRVar idxV) .nil) }
  | dty', _, _ => extCallExpr "arrLoadDyn" (encodeTy dty') hv

set_option linter.auxLemma false in
/-- `arrLoadCont` applied to any tail agrees with `ComCont.varBind` of
    `arrLoadExpr` (phrased per-applied-tail — over the singleton resolved-arg
    list the front actually emits; the implicit `{t}` of a bare `ComCont`
    equality won't synthesize). Both combinators are the same literal-pattern
    dependent match; casing the shape discriminants (`dty`, the slot types)
    reduces both by `rfl` in every case but `TU64 / memref / sword w`, where the
    `64` literal pattern compiles to a `dite (w = 64)` inside the two matchers:
    at `w = 64` both sides are again `rfl`, and at `w ≠ 64` unfolding the two
    matcher constants exposes that `dite` on both sides and `dif_neg` closes
    it. The equation lemmas of the catch-all arm are not used, since generating
    them for the literal pattern exceeds the heartbeat budget. -/
theorem arrLoadCont_eq {Γ : Ctx} (dty : TowerType)
    (st : CryptoTy) (sv : CVar Γ st) (it : CryptoTy) (iv : CVar Γ it)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys)
    {t : CryptoTy} (tail : Com catCryptDialect (encodeTy dty :: Γ) t) :
    arrLoadCont dty [⟨st, sv⟩] ⟨it, iv⟩ hv tail
      = ComCont.varBind (arrLoadExpr dty [⟨st, sv⟩] ⟨it, iv⟩ hv) tail := by
  cases dty <;>
    rcases st with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | nmem <;>
    rcases it with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | w | _ <;>
    try rfl
  rcases eq_or_ne w 64 with rfl | hw
  · rfl
  · unfold arrLoadCont arrLoadExpr
    delta arrLoadCont.match_1 arrLoadExpr.match_1
    simp only [dif_neg hw]

/-! ## 5c. `varBind`-factoring of the array **store** combinator

`arrStoreCont`'s memref branch is a `memrefSetDyn` `varBind` wrapped in a
`ComCont.castCtx` (a codomain transport, guarded by `encodeTy dty = .memref n`);
the fallback branches are a single `extCall "arrStoreDyn"` `varBind`. The
`castCtx`↔`varBind` naturality (`castCtx_varBind`) collapses the transport to a
`varBind` of the transported expression, so — exactly as for the load arm —
`arrStoreCont` factors as `ComCont.varBind (arrStoreExpr …)`, and the induction
case closes by `scalar_step`. -/

/-- Naturality of `ComCont.castCtx` against `ComCont.varBind`: transporting a
    `varBind` along a codomain-slot equality `hh : t = t'` (lifted to
    `hh ▸ (·::Γ)`) equals the `varBind` of the transported expression. General
    over `t`/`t'`, so it applies to the concrete `.memref n = encodeTy dty` cast
    by unification (a single `cases hh`, no case explosion). -/
theorem castCtx_varBind {Γ : Ctx} {t t' : CryptoTy} (hh : t = t')
    (e : Expr catCryptDialect Γ t) {s : CryptoTy}
    (tail : Com catCryptDialect (t' :: Γ) s) :
    ComCont.castCtx (congrArg (· :: Γ) hh) (ComCont.varBind e) tail
      = ComCont.varBind (hh ▸ e) tail := by
  cases hh; rfl

/-- Transport commutes with `Expr.denote`: `(hh ▸ e).denote V = hh ▸ (e.denote V)`
    for a codomain-slot equality `hh : t = t'`. General over `t`/`t'` (a single
    `cases hh`), the value-side twin of `castCtx_varBind`. -/
theorem expr_denote_cast {Γ : Ctx} {t t' : CryptoTy} (hh : t = t')
    (e : Expr catCryptDialect Γ t) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    (hh ▸ e).denote V = hh ▸ (e.denote V) := by
  cases hh; rfl

/-- Transport commutes with `Expr.denote` under `catCryptDenoteWith ls`. -/
theorem expr_denote_castWith (ls : SemLeafSpec) {Γ : Ctx} {t t' : CryptoTy} (hh : t = t')
    (e : Expr catCryptDialect Γ t) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    @Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ (hh ▸ e) V
      = hh ▸ (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ e V) := by
  cases hh; rfl

/-- The single expression `arrStoreCont` binds, in every branch. The memref
    branch is the `memrefSetDyn` expression transported from its natural codomain
    `.memref n` to the destination array's declared encoding `encodeTy dty`
    (guarded by `h : encodeTy dty = .memref n`); the fallbacks are the opaque
    `extCall "arrStoreDyn"`. -/
def arrStoreExpr {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    Expr catCryptDialect Γ (encodeTy dty) :=
  match resolvedArgs, idxSig with
  | [⟨.memref n, arrV⟩, ⟨.sword 64, srcV⟩], ⟨.sword 64, idxV⟩ =>
      let e : Expr catCryptDialect Γ (.memref n) :=
        { op := .memrefSetDyn n, retTy_eq := rfl,
          args := .cons (toVIRVar arrV)
            (.cons (toVIRVar idxV) (.cons (toVIRVar srcV) .nil)) }
      if h : encodeTy dty = .memref n then h.symm ▸ e
      else extCallExpr "arrStoreDyn" (encodeTy dty) hv
  | _, _ => extCallExpr "arrStoreDyn" (encodeTy dty) hv

/-- `arrStoreCont` applied to any tail agrees with `ComCont.varBind` of
    `arrStoreExpr` (phrased per-applied-tail, over the `[arr, src]`/`idx`
    resolved-arg list the front emits). The memref branch collapses its
    `castCtx` via `castCtx_varBind`; the fallbacks are already a bare `varBind`. -/
theorem arrStoreCont_eq {Γ : Ctx} (dty : TowerType)
    (at_ : CryptoTy) (av : CVar Γ at_) (stt : CryptoTy) (sv : CVar Γ stt)
    (it : CryptoTy) (iv : CVar Γ it)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys)
    {t : CryptoTy} (tail : Com catCryptDialect (encodeTy dty :: Γ) t) :
    arrStoreCont dty [⟨at_, av⟩, ⟨stt, sv⟩] ⟨it, iv⟩ hv tail
      = ComCont.varBind (arrStoreExpr dty [⟨at_, av⟩, ⟨stt, sv⟩] ⟨it, iv⟩ hv) tail := by
  rcases at_ with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | n <;>
    rcases stt with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ws | _ <;>
    rcases it with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | wi | _ <;>
    first
    | rfl
    | (-- Remaining: array slot `= .memref n`, source slot `= .sword ws`; the
       -- match is stuck on the symbolic `ws`. Split it (and, once it is `64`, the
       -- index width `wi`); every non-`(memref,64,64)` leaf collapses to the
       -- opaque `extCall` fallback, and the real branch closes by `castCtx_varBind`.
       rcases eq_or_ne ws 64 with rfl | hws
       · first
         | rfl
         | (rcases eq_or_ne wi 64 with rfl | hwi
            · simp only [arrStoreCont, arrStoreExpr]
              by_cases hmem : encodeTy dty = .memref n
              · simp only [dif_pos hmem]
                exact castCtx_varBind hmem.symm _ tail
              · simp only [dif_neg hmem]
            · simp [arrStoreCont, arrStoreExpr, CryptoTy.sword.injEq, hwi])
       · simp [arrStoreCont, arrStoreExpr, CryptoTy.sword.injEq, hws])

/-! ## 5d. The `RCallN` multi-dest fold

`RCallN` lowers via `loopCallNDestsD`, a left-to-right fold that binds each
destination through an `extCall (callNLeafName f i)` `varBind` at its output
index `i` (growing both the context and the `VarMap` by one slot per dest). The
homomorphism over the fold is proved by induction on the destination list —
generalizing the index `i` and the context `Γ` (each recursive step lands at
`i + 1` in `retTy :: Γ`) — with each step closing exactly like a `scalar_step`
composed via `ComCont.comp` (the `RSeq` spine), and the base case
(`ComCont.id`) closing like `RSkip`. -/

/-- Front-general preservation over the `RCallN` destination fold at the leaf oracle
    `ls`. Dest `i` binds the oracle at `callNLeafName fname i` and the arguments, so
    the emitted prefix denotes exactly `semCallNDestsL ls`. Induction on `dests`,
    generalizing the output index `i` and `Γ`/`vm`/`V`/`env`. -/
theorem loopCallNDestsD_denoteWith (ls : SemLeafSpec) (fname : String) (args : List Located) :
    ∀ (dests : List Located) {i : Nat} {Γ : Ctx} (vm : VarMap Γ)
      (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopCallNDestsD fname args vm dests i = some o →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' (semCallNDestsL ls fname args dests i env) ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  intro dests
  induction dests with
  | nil =>
      intro i Γ vm V env o hc htr
      simp only [loopCallNDestsD] at htr
      obtain rfl := Option.some.inj htr
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | cons d rest ih =>
      intro i Γ vm V env o hc htr
      rcases hra : resolveLocatedArgs vm args with _ | resolvedArgs
      · simp [loopCallNDestsD, hra] at htr
      · simp only [loopCallNDestsD, hra] at htr
        rcases hrest : loopCallNDestsD fname args (vm.bind d.locVar) rest (i + 1) with _ | oRest
        · rw [hrest] at htr; simp at htr
        · rw [hrest] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          obtain ⟨hcons1, hcont1⟩ :=
            scalar_stepWith ls vm V env hc d.locVar
              (extCallExpr (callNLeafName fname i) (encodeTy d.locDst)
                (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hc args resolvedArgs hra]
            at hcons1 hcont1
          obtain ⟨V', hc', hcont2⟩ :=
            ih (vm.bind d.locVar) (V.extend _) _ oRest hcons1 hrest
          refine ⟨V', hc', ?_⟩
          intro t tail
          obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
          obtain ⟨com, hcom, hden⟩ := hcont1 com2
          refine ⟨com, ?_, ?_⟩
          · show ComCont.comp (ComCont.varBind _) oRest.cont tail = some com
            simp only [ComCont.comp, hcom2, hcom]
          · exact hden.trans hden2

/-- Front-general preservation over the `RCallN` destination fold
    (`loopCallNDestsD_denoteWith` at `defaultLeaf`). -/
theorem loopCallNDestsD_denote (fname : String) (args : List Located) :
    ∀ (dests : List Located) {i : Nat} {Γ : Ctx} (vm : VarMap Γ)
      (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopCallNDestsD fname args vm dests i = some o →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' (semCallNDests dests env) ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro dests i Γ vm V env o hc htr
  have h := loopCallNDestsD_denoteWith defaultLeaf fname args dests vm V env o hc htr
  rwa [catCryptDenoteWith_default, semCallNDestsL_default] at h

/-! ## 5e. Fresh-temp bookkeeping for the `SExpr`-recursion homomorphism

The `RScalarSetExpr` front lowers an `SExpr` into a chain of `varBind`s over
FRESH temps `tmpName k` (counters strictly increasing). To prove the emitted
chain denotes `SExpr.evalBV`, we thread three invariants alongside `ConsistentS`:

* `FreshFrom env cnt` — `env` has NO temp bound at index `≥ cnt` (the fresh
  region the chain will use);
* `OnlyTmpBelow env env2 cnt` — `env2` agrees with `env` everywhere EXCEPT temps
  at index `≥ cnt` (the chain only writes fresh temps, never a source read);
* `ResultOK nm cnt'` — the result name is a source name or a temp of index
  `< cnt'` (so a *later* fresh temp never overwrites it).

Together with `tmpName` injectivity they give the non-collision facts the
homomorphism needs. -/

/-- `env` binds no temporary at index `≥ cnt`. -/
def FreshFrom (env : SEnvScalar) (cnt : Nat) : Prop :=
  ∀ k, cnt ≤ k → env (TranslateDialectDirectArms.tmpName k) = none

/-- `env2` agrees with `env` off the fresh-temp region `{tmpName k : k ≥ cnt}`. -/
def OnlyTmpBelow (env env2 : SEnvScalar) (cnt : Nat) : Prop :=
  ∀ s, (¬ isTmpName s ∨ ∃ k, k < cnt ∧ s = TranslateDialectDirectArms.tmpName k) → env2 s = env s

/-- The result name is a source name, or a temp of index `< cnt'`. -/
def ResultOK (nm : String) (cnt' : Nat) : Prop :=
  ¬ isTmpName nm ∨ ∃ k, k < cnt' ∧ nm = TranslateDialectDirectArms.tmpName k

theorem tmpName_ne {k c : Nat} (h : k ≠ c) :
    TranslateDialectDirectArms.tmpName k ≠ TranslateDialectDirectArms.tmpName c :=
  fun he => h (tmpName_injective he)

theorem ne_tmpName_of_not_isTmp {s : String} (h : ¬ isTmpName s) (c : Nat) :
    s ≠ TranslateDialectDirectArms.tmpName c :=
  fun he => h ⟨c, he⟩

theorem onlyTmpBelow_refl (env : SEnvScalar) (cnt : Nat) : OnlyTmpBelow env env cnt :=
  fun _ _ => rfl

theorem onlyTmpBelow_trans {env e1 e2 : SEnvScalar} {cnt c1 : Nat}
    (h1 : OnlyTmpBelow env e1 cnt) (h2 : OnlyTmpBelow e1 e2 c1) (hle : cnt ≤ c1) :
    OnlyTmpBelow env e2 cnt := by
  intro s hs
  have hs' : ¬ isTmpName s ∨ ∃ k, k < c1 ∧ s = TranslateDialectDirectArms.tmpName k := by
    rcases hs with h | ⟨k, hk, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, by omega, rfl⟩
  rw [h2 s hs']
  exact h1 s hs

theorem onlyTmpBelow_upd {env e2 : SEnvScalar} {cnt c : Nat} {w : BitVec 64}
    (h : OnlyTmpBelow env e2 cnt) (hc : cnt ≤ c) :
    OnlyTmpBelow env (e2.upd (TranslateDialectDirectArms.tmpName c) (t := .sword 64) w) cnt := by
  intro s hs
  have hne : s ≠ TranslateDialectDirectArms.tmpName c := by
    rcases hs with h1 | ⟨k, hk, rfl⟩
    · exact ne_tmpName_of_not_isTmp h1 c
    · exact tmpName_ne (by omega)
  simp only [SEnvScalar.upd, if_neg hne]
  exact h s hs

theorem freshFrom_upd_succ {env : SEnvScalar} {c : Nat} {w : BitVec 64}
    (h : FreshFrom env c) :
    FreshFrom (env.upd (TranslateDialectDirectArms.tmpName c) (t := .sword 64) w) (c + 1) := by
  intro k hk
  have hne : TranslateDialectDirectArms.tmpName k ≠ TranslateDialectDirectArms.tmpName c :=
    tmpName_ne (by omega)
  simp only [SEnvScalar.upd, if_neg hne]
  exact h k (by omega)

/-- `ConsistentS` bridges the front's `lookupU64` to the env word-reader
    `envReadU64`. -/
theorem consistentS_readU64 {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) (nm : String) {v : CVar Γ (.sword 64)}
    (h : TranslateDialectDirectArms.lookupU64 vm nm = some v) :
    envReadU64 env nm = some ((toVIRVar v).lookup V) := by
  have hlk := hc nm
  simp only [TranslateDialectDirectArms.lookupU64] at h
  split at h
  · next v' heq =>
      simp only [Option.some.injEq] at h
      subst h
      rw [heq] at hlk
      simp only [Option.map_some] at hlk
      simp only [envReadU64, ← hlk]
  · exact absurd h (by simp)

/-- `envReadU64` and `envReader` read the same `.sword 64` slot. -/
theorem envReadU64_reader {env : SEnvScalar} {nm : String} {w : BitVec 64}
    (h : envReadU64 env nm = some w) : envReader env nm = w := by
  simp only [envReadU64] at h
  simp only [envReader]
  split at h <;> simp_all

/-- Reading back a just-bound `.sword 64` temp. -/
theorem envReadU64_upd_self (env : SEnvScalar) (nm : String) (w : BitVec 64) :
    envReadU64 (env.upd nm (t := .sword 64) w) nm = some w := by
  simp [envReadU64, SEnvScalar.upd]

/-- Stability: a name in the preserved set keeps its `envReadU64` value. -/
theorem readU64_stable {env e2 : SEnvScalar} {cnt : Nat} {nm : String}
    (h : OnlyTmpBelow env e2 cnt) (hnm : ResultOK nm cnt) :
    envReadU64 e2 nm = envReadU64 env nm := by
  have : e2 nm = env nm := h nm hnm
  simp only [envReadU64, this]

/-- `SExpr.evalBV` congruence: readers agreeing on non-temp names agree on a
    `srcClean` expression (its variables are all non-temp). -/
theorem evalBV_congr (β1 β2 : String → BitVec 64) :
    ∀ (e : SExpr), (∀ s, ¬ isTmpName s → β1 s = β2 s) → srcClean e →
      SExpr.evalBV β1 e = SExpr.evalBV β2 e := by
  intro e
  induction e with
  | SVar x => intro hβ hcl; simp only [SExpr.evalBV]; exact hβ x hcl
  | SLit n => intro _ _; rfl
  | SAdd a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SSub a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SMul a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SAnd a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SXor a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SShl a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SShr a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SMulHiU a b iha ihb => intro hβ hcl; simp only [SExpr.evalBV, iha hβ hcl.1, ihb hβ hcl.2]
  | SLt a b iha ihb => intro _ hcl; exact hcl.elim
  | SAsr a b iha ihb => intro _ hcl; exact hcl.elim
  | SMulS a b iha ihb => intro _ hcl; exact hcl.elim
  | SMulHiS a b iha ihb => intro _ hcl; exact hcl.elim
  | SLimb v i => intro _ _; rfl

/-- The `mulHiC` ↔ `sexprMulHiU` bridge: the dialect's high-word multiply
    (`Nat`-division by `2^64` of the full product) agrees with `SExpr.evalBV`'s
    `SMulHiU` arm (`sexprMulHiU`, a `>>> 64` over the mod-`2^64`-reduced
    operands) on `u64` words — the reductions are no-ops (`BitVec.isLt`) and the
    shift is the same division (`Nat.shiftRight_eq_div_pow`). -/
theorem mulHiC_eq_sexprMulHiU (x y : BitVec 64) :
    mulHiC x y
      = BitVec.ofNat 64 (CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU x.toNat y.toNat) := by
  simp [mulHiC, CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]

/-! ## 5e′. The constant-time word select chain (`RSelect`) -/

/-- A name the env binds at type `t` is bound to a slot of type `t` in a consistent
    `VarMap`. -/
theorem consistentS_bound {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) {s : String} {t : CryptoTy} {v : ⟦t⟧}
    (h : env s = some ⟨t, v⟩) : ∃ cv, vm.lookup s = some ⟨t, cv⟩ := by
  have hs := hc s
  rw [h] at hs
  cases hl : vm.lookup s with
  | none => rw [hl] at hs; simp at hs
  | some p =>
      obtain ⟨t', cv⟩ := p
      rw [hl] at hs
      simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hs
      obtain ⟨rfl, _⟩ := hs
      exact ⟨cv, rfl⟩

/-- The mask chain of `selectMaskCont` computes `selectWord`: for `s ≠ 0` the
    top bit of `s ||| (0 - s)` is set, so the mask `0 - ((s ||| (0 - s)) >>> 63)`
    is all ones; for `s = 0` it is zero. -/
theorem selectWord_mask (s a c : BitVec 64) :
    a ^^^ ((a ^^^ c) &&& (0 - BitVec.ushiftRight (s ||| (0 - s)) 63))
      = selectWord s a c := by
  unfold selectWord
  by_cases hs : s = 0#64
  · subst hs; simp
  · rw [if_neg hs]
    have hb : BitVec.ushiftRight (s ||| (0 - s)) 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      have h1 : s.toNat ≠ 0 := fun h => hs (BitVec.eq_of_toNat_eq (by simpa using h))
      have hlt := s.isLt
      have hneg : (0 - s).toNat = 2 ^ 64 - s.toNat := by
        rw [BitVec.toNat_sub]; simp; omega
      have hor : (s ||| (0 - s)).toNat < 2 ^ 64 := (s ||| (0 - s)).isLt
      have hge : 2 ^ 63 ≤ (s ||| (0 - s)).toNat := by
        rw [BitVec.toNat_or]
        by_cases hh : 2 ^ 63 ≤ s.toNat
        · exact Nat.le_trans hh Nat.left_le_or
        · exact Nat.le_trans (by rw [hneg]; omega) Nat.right_le_or
      show (s ||| (0 - s)).toNat >>> 63 = (1 : BitVec 64).toNat
      rw [Nat.shiftRight_eq_div_pow]
      have h1' : (1 : BitVec 64).toNat = 1 := rfl
      rw [h1']
      omega
    rw [hb]
    have hm : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
    rw [hm, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The select chain binds `dst` to `selectWord` of the three source slots,
    keeps every other name consistent (the seven temporaries are anonymous), and
    applied to any tail denotes that tail at the extended valuation, under
    `catCryptDenoteWith ls` for every leaf oracle `ls` (the chain holds no leaf). -/
theorem selectMaskCont_denoteWith (ls : SemLeafSpec) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) (sV aV cV : CVar Γ (.sword 64)) :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) (selectCtx Γ),
      ConsistentS (selectVm vm dst) V'
        (env.upd dst (t := .sword 64) (selectWord ((toVIRVar sV).lookup V)
          ((toVIRVar aV).lookup V) ((toVIRVar cV).lookup V))) ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect (selectCtx Γ) t),
        ∃ com, selectMaskCont sV aV cV tail = some com ∧
          @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
            = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  let s : BitVec 64 := (toVIRVar sV).lookup V
  let a : BitVec 64 := (toVIRVar aV).lookup V
  let c : BitVec 64 := (toVIRVar cV).lookup V
  let z : BitVec 64 := 0
  let n : BitVec 64 := z - s
  let o : BitVec 64 := s ||| n
  let b : BitVec 64 := BitVec.ushiftRight o 63
  let m : BitVec 64 := z - b
  let x : BitVec 64 := a ^^^ c
  let y : BitVec 64 := x &&& m
  let ext := fun {Δ : Ctx} (W : Ctxt.Valuation (d := catCryptDialect) Δ) (v : BitVec 64) =>
    Ctxt.Valuation.extend (d := catCryptDialect) (t := CryptoTy.sword 64) W v
  let V₇ := ext (ext (ext (ext (ext (ext (ext V z) n) o) b) m) x) y
  have h₇ : ConsistentS ((((((((vm.weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
      (t := .sword 64)).weaken (t := .sword 64)).weaken (t := .sword 64)).weaken
      (t := .sword 64)).weaken (t := .sword 64))) V₇ env :=
    have hw : ∀ {Δ : Ctx} (vm' : VarMap Δ) (W : Ctxt.Valuation (d := catCryptDialect) Δ),
        ConsistentS vm' W env → ∀ v : BitVec 64,
          ConsistentS (vm'.weaken (t := .sword 64)) (ext W v) env :=
      fun vm' W h v => consistentS_weaken (t := .sword 64) vm' W env h v
    hw _ _ (hw _ _ (hw _ _ (hw _ _ (hw _ _ (hw _ _ (hw vm V hc z) n) o) b) m) x) y
  refine ⟨ext V₇ (selectWord s a c), ?_, ?_⟩
  · exact (scalar_step _ V₇ env h₇ dst
      ({ op := .bvConst 64 (selectWord s a c), retTy_eq := rfl, args := .nil } :
        Expr catCryptDialect _ (.sword 64))).1
  · intro t tail
    refine ⟨_, rfl, ?_⟩
    exact congrArg
      (fun v => @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail (ext V₇ v))
      (selectWord_mask s a c)

/-- The select chain binds `dst` to `selectWord` of the three source slots
    (`selectMaskCont_denoteWith` at `defaultLeaf`). -/
theorem selectMaskCont_denote {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) (sV aV cV : CVar Γ (.sword 64)) :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) (selectCtx Γ),
      ConsistentS (selectVm vm dst) V'
        (env.upd dst (t := .sword 64) (selectWord ((toVIRVar sV).lookup V)
          ((toVIRVar aV).lookup V) ((toVIRVar cV).lookup V))) ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect (selectCtx Γ) t),
        ∃ com, selectMaskCont sV aV cV tail = some com ∧
          com.denote V = tail.denote V' := by
  have h := selectMaskCont_denoteWith defaultLeaf vm V env hc dst sV aV cV
  rwa [catCryptDenoteWith_default] at h

/-- The `ite` of `selectCmpCont` on the decided bit `s = 0` is `selectWord`. -/
theorem selectWord_cmp (s a c : BitVec 64) :
    (if (decide (s = 0#64) : Bool) then a else c) = selectWord s a c := by
  unfold selectWord
  by_cases hs : s = 0#64 <;> simp [hs]

/-- The comparison select binds `dst` to `selectWord` of the three source slots,
    keeps every other name consistent (the zero word and the comparison bit are
    anonymous), and applied to any tail denotes that tail at the extended
    valuation, under `catCryptDenoteWith ls` for every leaf oracle `ls` (the
    prefix holds no leaf). -/
theorem selectCmpCont_denoteWith (ls : SemLeafSpec) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) (sV aV cV : CVar Γ (.sword 64)) :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) (selectCmpCtx Γ),
      ConsistentS (selectCmpVm vm dst) V'
        (env.upd dst (t := .sword 64) (selectWord ((toVIRVar sV).lookup V)
          ((toVIRVar aV).lookup V) ((toVIRVar cV).lookup V))) ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect (selectCmpCtx Γ) t),
        ∃ com, selectCmpCont sV aV cV tail = some com ∧
          @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
            = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  let s : BitVec 64 := (toVIRVar sV).lookup V
  let a : BitVec 64 := (toVIRVar aV).lookup V
  let c : BitVec 64 := (toVIRVar cV).lookup V
  let V₁ := Ctxt.Valuation.extend (d := catCryptDialect) (t := CryptoTy.sword 64) V (0 : BitVec 64)
  let V₂ := Ctxt.Valuation.extend (d := catCryptDialect) (t := CryptoTy.bit) V₁
    (decide (s = 0#64))
  have h₂ : ConsistentS ((vm.weaken (t := .sword 64)).weaken (t := .bit)) V₂ env :=
    consistentS_weaken (t := .bit) _ V₁ env
      (consistentS_weaken (t := .sword 64) vm V env hc (0 : BitVec 64)) (decide (s = 0#64))
  refine ⟨Ctxt.Valuation.extend (d := catCryptDialect) (t := CryptoTy.sword 64) V₂
    (selectWord s a c), ?_, ?_⟩
  · exact (scalar_step _ V₂ env h₂ dst
      ({ op := .bvConst 64 (selectWord s a c), retTy_eq := rfl, args := .nil } :
        Expr catCryptDialect _ (.sword 64))).1
  · intro t tail
    refine ⟨_, rfl, ?_⟩
    exact congrArg
      (fun v => @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail
        (Ctxt.Valuation.extend (d := catCryptDialect) (t := CryptoTy.sword 64) V₂ v))
      (selectWord_cmp s a c)

/-- The comparison select binds `dst` to `selectWord` of the three source slots
    (`selectCmpCont_denoteWith` at `defaultLeaf`). -/
theorem selectCmpCont_denote {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnvScalar)
    (hc : ConsistentS vm V env) (dst : String) (sV aV cV : CVar Γ (.sword 64)) :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) (selectCmpCtx Γ),
      ConsistentS (selectCmpVm vm dst) V'
        (env.upd dst (t := .sword 64) (selectWord ((toVIRVar sV).lookup V)
          ((toVIRVar aV).lookup V) ((toVIRVar cV).lookup V))) ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect (selectCmpCtx Γ) t),
        ∃ com, selectCmpCont sV aV cV tail = some com ∧
          com.denote V = tail.denote V' := by
  have h := selectCmpCont_denoteWith defaultLeaf vm V env hc dst sV aV cV
  rwa [catCryptDenoteWith_default] at h

/-! ## 6. Front-general scalar preservation over the straight-line fragment -/

/-! ## 5f. The `SExpr`-recursion homomorphism (`RScalarSetExpr`) -/

/-- **The `SExpr`-recursion denotation homomorphism.** For a `srcClean` `SExpr`
    lowered by `lowerSExpr` from a `ConsistentS` state with a fresh temp region,
    the emitted `ComCont` chain denotes exactly its env-mirror `semLowerSExpr`,
    and its result slot resolves to the closed-form word evaluator
    `SExpr.evalBV (envReader env) e`. Induction on `SExpr`; each binary node is a
    fresh `varBind` composed via `ComCont.comp` on the two sub-chains, its value
    reconciled through `consistentS_readU64` + the fresh-temp non-collision
    lemmas (`readU64_stable`, `onlyTmpBelow_*`, `freshFrom_upd_succ`) + the
    reader congruence `evalBV_congr`. The shift arms add a 2-way `split` on the
    front's inline amount-shape match (immediate `bvShiftL`/`bvShiftR 64 k` on a
    literal amount, variable `bvShiftLV`/`bvShiftRV 64` otherwise); the literal
    branch reconciles `k = (BitVec.ofNat 64 k).toNat` from `srcClean`'s
    `k < 2^64` bound. `SMulHiU` closes via `mulHiC_eq_sexprMulHiU`. The chain holds
    no leaf, and the statement is made under `catCryptDenoteWith ls` for every leaf
    oracle `ls`. -/
theorem lowerSExpr_denoteWith (ls : SemLeafSpec) (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env : SEnvScalar) (cnt : Nat) (o : DTransOut Γ) (nm : String) (cnt' : Nat),
      ConsistentS vm V env → srcClean e →
      TranslateDialectDirectArms.lowerSExpr vm cnt e = some (o, nm, cnt') →
      ∃ (V' : Ctxt.Valuation (d := catCryptDialect) o.Γ') (env2 : SEnvScalar),
        semLowerSExpr env cnt e = some (env2, nm, cnt') ∧
        cnt ≤ cnt' ∧
        ConsistentS o.vm V' env2 ∧
        (∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V') ∧
        OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧
        envReadU64 env2 nm = some (SExpr.evalBV (envReader env) e) := by
  induction e with
  | SVar x =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · next w hlk =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hlow
          obtain ⟨rfl, rfl, rfl⟩ := hlow
          have hread := consistentS_readU64 hc x hlk
          refine ⟨V, env, ?_, le_refl _, hc, fun tail => ⟨tail, rfl, rfl⟩,
            onlyTmpBelow_refl env cnt, Or.inl hclean, ?_⟩
          · simp only [semLowerSExpr, hread]
          · simp only [SExpr.evalBV]
            rw [envReadU64_reader hread]; exact hread
      · exact absurd hlow (by simp)
  | SLit n =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr, Option.some.injEq, Prod.mk.injEq] at hlow
      obtain ⟨rfl, rfl, rfl⟩ := hlow
      have hstep := scalar_stepWith ls vm V env hc (TranslateDialectDirectArms.tmpName cnt)
        ({ op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil } :
          Expr catCryptDialect Γ (.sword 64))
      obtain ⟨hcons, hcont⟩ := hstep
      refine ⟨V.extend (BitVec.ofNat 64 n),
        env.upd (TranslateDialectDirectArms.tmpName cnt) (t := .sword 64) (BitVec.ofNat 64 n),
        rfl, Nat.le_succ _, hcons, ?_,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩,
        by rw [envReadU64_upd_self]; rfl⟩
      intro t tail
      obtain ⟨com, hcom, hden⟩ := hcont tail
      exact ⟨com, by simpa [TranslateDialectDirectArms.pushVarBind, ComCont.comp,
        ComCont.id] using! hcom, hden⟩
  | SAdd a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eAdd : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvAdd 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heAdd
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eAdd
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eAdd.denote V₂
                      = SExpr.evalBV (envReader env) a + SExpr.evalBV (envReader env) b := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (· + ·)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eAdd.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eAdd.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eAdd.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SSub a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvSub 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eOp.denote V₂
                      = SExpr.evalBV (envReader env) a - SExpr.evalBV (envReader env) b := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (· - ·)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eOp.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SMul a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvMul 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eOp.denote V₂
                      = SExpr.evalBV (envReader env) a * SExpr.evalBV (envReader env) b := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (· * ·)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eOp.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SShr a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  -- 2-way split on the emitted op's amount shape: a literal
                  -- amount `SLit k` emits the immediate `bvShiftR 64 k`, a
                  -- runtime amount the variable `bvShiftRV 64`.
                  split at hlow
                  · next k =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                      obtain ⟨rfl, rfl, rfl⟩ := hlow
                      obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                        iha vm V env cnt oa na c1 hc sa hra
                      obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                        ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                      have hva := consistentS_readU64 hcB na hla
                      have hvb := consistentS_readU64 hcB nb hlb
                      set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                        { op := .bvShiftR 64 k, retTy_eq := rfl,
                          args := .cons (toVIRVar va) .nil } with heOp
                      obtain ⟨hcons, hcontFin⟩ :=
                        scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                      have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                        have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                          rw [readU64_stable hotbB hrokA]; exact hvalA
                        rw [hva] at h1; exact Option.some.inj h1
                      have hvb_ev : (toVIRVar vb).lookup V₂
                          = SExpr.evalBV (envReader env) (SExpr.SLit k) := by
                        have h1 : envReadU64 env2 nb
                            = some (SExpr.evalBV (envReader env) (SExpr.SLit k)) := hvalB
                        rw [hvb] at h1; exact Option.some.inj h1
                      have hk : (SExpr.evalBV (envReader env) (SExpr.SLit k)).toNat = k := by
                        have hklt : k < 2 ^ 64 := sb
                        simp only [SExpr.evalBV, BitVec.toNat_ofNat]
                        omega
                      have hden : eOp.denote V₂
                          = SExpr.evalBV (envReader env) a
                              >>> (SExpr.evalBV (envReader env) (SExpr.SLit k)).toNat := by
                        rw [hk, ← hva_ev]; rfl
                      have hbin : binNode env2 na nb c2 (fun x y => x >>> y.toNat)
                          = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                              (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                        simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                      refine ⟨V₂.extend (eOp.denote V₂),
                        env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                        ?_, by omega, hcons, ?_,
                        onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                        Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                      · -- fold the inner `semLowerSExpr (SLit k)` computation back
                        -- through `hsemB` (b is concrete here, so the def-equation
                        -- would otherwise race the IH rewrite)
                        have hinj : env1.upd (TranslateDialectDirectArms.tmpName c1)
                              (t := .sword 64) (BitVec.ofNat 64 k) = env2
                            ∧ TranslateDialectDirectArms.tmpName c1 = nb ∧ c1 + 1 = c2 := by
                          simpa [semLowerSExpr] using hsemB
                        obtain ⟨rfl, rfl, rfl⟩ := hinj
                        simp only [semLowerSExpr, hsemA, hbin]
                      · intro t tail
                        obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                        obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                        obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                        refine ⟨comA, ?_, ?_⟩
                        · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                            = some comA
                          simp only [ComCont.comp, hcomV, hcomB, hcomA]
                        · rw [hdenA, hdenB]; exact hdenV
                      · rw [envReadU64_upd_self, hden]; rfl
                  · -- runtime amount: variable `bvShiftRV 64`
                      simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                      obtain ⟨rfl, rfl, rfl⟩ := hlow
                      obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                        iha vm V env cnt oa na c1 hc sa hra
                      obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                        ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                      have hva := consistentS_readU64 hcB na hla
                      have hvb := consistentS_readU64 hcB nb hlb
                      set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                        { op := .bvShiftRV 64, retTy_eq := rfl,
                          args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                      obtain ⟨hcons, hcontFin⟩ :=
                        scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                      have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                        have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                          rw [readU64_stable hotbB hrokA]; exact hvalA
                        rw [hva] at h1; exact Option.some.inj h1
                      have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                        have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                          evalBV_congr _ _ b
                            (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                        have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                          rw [hvalB, hcongr]
                        rw [hvb] at h1; exact Option.some.inj h1
                      have hden : eOp.denote V₂
                          = SExpr.evalBV (envReader env) a
                              >>> (SExpr.evalBV (envReader env) b).toNat := by
                        rw [← hva_ev, ← hvb_ev]; rfl
                      have hbin : binNode env2 na nb c2 (fun x y => x >>> y.toNat)
                          = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                              (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                        simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                      refine ⟨V₂.extend (eOp.denote V₂),
                        env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                        ?_, by omega, hcons, ?_,
                        onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                        Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                      · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                      · intro t tail
                        obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                        obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                        obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                        refine ⟨comA, ?_, ?_⟩
                        · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                            = some comA
                          simp only [ComCont.comp, hcomV, hcomB, hcomA]
                        · rw [hdenA, hdenB]; exact hdenV
                      · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SShl a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  -- 2-way split on the emitted op's amount shape: a literal
                  -- amount `SLit k` emits the immediate `bvShiftL 64 k`, a
                  -- runtime amount the variable `bvShiftLV 64`.
                  split at hlow
                  · next k =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                      obtain ⟨rfl, rfl, rfl⟩ := hlow
                      obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                        iha vm V env cnt oa na c1 hc sa hra
                      obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                        ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                      have hva := consistentS_readU64 hcB na hla
                      have hvb := consistentS_readU64 hcB nb hlb
                      set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                        { op := .bvShiftL 64 k, retTy_eq := rfl,
                          args := .cons (toVIRVar va) .nil } with heOp
                      obtain ⟨hcons, hcontFin⟩ :=
                        scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                      have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                        have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                          rw [readU64_stable hotbB hrokA]; exact hvalA
                        rw [hva] at h1; exact Option.some.inj h1
                      have hvb_ev : (toVIRVar vb).lookup V₂
                          = SExpr.evalBV (envReader env) (SExpr.SLit k) := by
                        have h1 : envReadU64 env2 nb
                            = some (SExpr.evalBV (envReader env) (SExpr.SLit k)) := hvalB
                        rw [hvb] at h1; exact Option.some.inj h1
                      have hk : (SExpr.evalBV (envReader env) (SExpr.SLit k)).toNat = k := by
                        have hklt : k < 2 ^ 64 := sb
                        simp only [SExpr.evalBV, BitVec.toNat_ofNat]
                        omega
                      have hden : eOp.denote V₂
                          = SExpr.evalBV (envReader env) a
                              <<< (SExpr.evalBV (envReader env) (SExpr.SLit k)).toNat := by
                        rw [hk, ← hva_ev]; rfl
                      have hbin : binNode env2 na nb c2 (fun x y => x <<< y.toNat)
                          = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                              (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                        simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                      refine ⟨V₂.extend (eOp.denote V₂),
                        env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                        ?_, by omega, hcons, ?_,
                        onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                        Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                      · -- fold the inner `semLowerSExpr (SLit k)` computation back
                        -- through `hsemB` (b is concrete here, so the def-equation
                        -- would otherwise race the IH rewrite)
                        have hinj : env1.upd (TranslateDialectDirectArms.tmpName c1)
                              (t := .sword 64) (BitVec.ofNat 64 k) = env2
                            ∧ TranslateDialectDirectArms.tmpName c1 = nb ∧ c1 + 1 = c2 := by
                          simpa [semLowerSExpr] using hsemB
                        obtain ⟨rfl, rfl, rfl⟩ := hinj
                        simp only [semLowerSExpr, hsemA, hbin]
                      · intro t tail
                        obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                        obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                        obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                        refine ⟨comA, ?_, ?_⟩
                        · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                            = some comA
                          simp only [ComCont.comp, hcomV, hcomB, hcomA]
                        · rw [hdenA, hdenB]; exact hdenV
                      · rw [envReadU64_upd_self, hden]; rfl
                  · -- runtime amount: variable `bvShiftLV 64`
                      simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                      obtain ⟨rfl, rfl, rfl⟩ := hlow
                      obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                        iha vm V env cnt oa na c1 hc sa hra
                      obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                        ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                      have hva := consistentS_readU64 hcB na hla
                      have hvb := consistentS_readU64 hcB nb hlb
                      set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                        { op := .bvShiftLV 64, retTy_eq := rfl,
                          args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                      obtain ⟨hcons, hcontFin⟩ :=
                        scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                      have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                        have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                          rw [readU64_stable hotbB hrokA]; exact hvalA
                        rw [hva] at h1; exact Option.some.inj h1
                      have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                        have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                          evalBV_congr _ _ b
                            (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                        have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                          rw [hvalB, hcongr]
                        rw [hvb] at h1; exact Option.some.inj h1
                      have hden : eOp.denote V₂
                          = SExpr.evalBV (envReader env) a
                              <<< (SExpr.evalBV (envReader env) b).toNat := by
                        rw [← hva_ev, ← hvb_ev]; rfl
                      have hbin : binNode env2 na nb c2 (fun x y => x <<< y.toNat)
                          = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                              (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                        simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                      refine ⟨V₂.extend (eOp.denote V₂),
                        env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                        ?_, by omega, hcons, ?_,
                        onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                        Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                      · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                      · intro t tail
                        obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                        obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                        obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                        refine ⟨comA, ?_, ?_⟩
                        · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                            = some comA
                          simp only [ComCont.comp, hcomV, hcomB, hcomA]
                        · rw [hdenA, hdenB]; exact hdenV
                      · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SAnd a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvAnd 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eOp.denote V₂
                      = SExpr.evalBV (envReader env) a &&& SExpr.evalBV (envReader env) b := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (· &&& ·)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eOp.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SXor a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvXor 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eOp.denote V₂
                      = SExpr.evalBV (envReader env) a ^^^ SExpr.evalBV (envReader env) b := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (· ^^^ ·)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eOp.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden]; rfl
              · exact absurd hlow (by simp)
  | SMulHiU a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      obtain ⟨sa, sb⟩ := hclean
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨V₁, env1, hsemA, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ :=
                    iha vm V env cnt oa na c1 hc sa hra
                  obtain ⟨V₂, env2, hsemB, hleB, hcB, hcontB, hotbB, hrokB, hvalB⟩ :=
                    ihb oa.vm V₁ env1 c1 ob nb c2 hcA sb hrb
                  have hva := consistentS_readU64 hcB na hla
                  have hvb := consistentS_readU64 hcB nb hlb
                  set eOp : Expr catCryptDialect ob.Γ' (.sword 64) :=
                    { op := .bvMulHi 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } with heOp
                  obtain ⟨hcons, hcontFin⟩ :=
                    scalar_stepWith ls ob.vm V₂ env2 hcB (TranslateDialectDirectArms.tmpName c2) eOp
                  have hva_ev : (toVIRVar va).lookup V₂ = SExpr.evalBV (envReader env) a := by
                    have h1 : envReadU64 env2 na = some (SExpr.evalBV (envReader env) a) := by
                      rw [readU64_stable hotbB hrokA]; exact hvalA
                    rw [hva] at h1; exact Option.some.inj h1
                  have hvb_ev : (toVIRVar vb).lookup V₂ = SExpr.evalBV (envReader env) b := by
                    have hcongr : SExpr.evalBV (envReader env1) b = SExpr.evalBV (envReader env) b :=
                      evalBV_congr _ _ b
                        (fun t ht => by simp only [envReader]; rw [hotbA t (Or.inl ht)]) sb
                    have h1 : envReadU64 env2 nb = some (SExpr.evalBV (envReader env) b) := by
                      rw [hvalB, hcongr]
                    rw [hvb] at h1; exact Option.some.inj h1
                  have hden : eOp.denote V₂
                      = mulHiC (SExpr.evalBV (envReader env) a)
                          (SExpr.evalBV (envReader env) b) := by
                    rw [← hva_ev, ← hvb_ev]; rfl
                  have hbin : binNode env2 na nb c2 (fun x y => mulHiC x y)
                      = some (env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64)
                          (eOp.denote V₂), TranslateDialectDirectArms.tmpName c2, c2 + 1) := by
                    simp only [binNode, hva, hvb]; rw [hva_ev, hvb_ev, ← hden]
                  refine ⟨V₂.extend (eOp.denote V₂),
                    env2.upd (TranslateDialectDirectArms.tmpName c2) (t := .sword 64) (eOp.denote V₂),
                    ?_, by omega, hcons, ?_,
                    onlyTmpBelow_upd (onlyTmpBelow_trans hotbA hotbB hleA) (by omega),
                    Or.inr ⟨c2, Nat.lt_succ_self _, rfl⟩, ?_⟩
                  · simp only [semLowerSExpr, hsemA, hsemB, hbin]
                  · intro t tail
                    obtain ⟨comV, hcomV, hdenV⟩ := hcontFin tail
                    obtain ⟨comB, hcomB, hdenB⟩ := hcontB comV
                    obtain ⟨comA, hcomA, hdenA⟩ := hcontA comB
                    refine ⟨comA, ?_, ?_⟩
                    · show ComCont.comp (ComCont.comp oa.cont ob.cont) (ComCont.varBind _) tail
                        = some comA
                      simp only [ComCont.comp, hcomV, hcomB, hcomA]
                    · rw [hdenA, hdenB]; exact hdenV
                  · rw [envReadU64_upd_self, hden, mulHiC_eq_sexprMulHiU]; rfl
              · exact absurd hlow (by simp)
  | SLt a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow; exact absurd hlow (by simp)
  | SAsr a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow; exact absurd hlow (by simp)
  | SMulS a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow; exact absurd hlow (by simp)
  | SMulHiS a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow; exact absurd hlow (by simp)
  | SLimb x i =>
      intro Γ vm V env cnt o nm cnt' hc hclean hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow; exact absurd hlow (by simp)

/-- The `SExpr`-recursion denotation homomorphism (`lowerSExpr_denoteWith` at
    `defaultLeaf`). -/
theorem lowerSExpr_denote (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env : SEnvScalar) (cnt : Nat) (o : DTransOut Γ) (nm : String) (cnt' : Nat),
      ConsistentS vm V env → srcClean e →
      TranslateDialectDirectArms.lowerSExpr vm cnt e = some (o, nm, cnt') →
      ∃ (V' : Ctxt.Valuation (d := catCryptDialect) o.Γ') (env2 : SEnvScalar),
        semLowerSExpr env cnt e = some (env2, nm, cnt') ∧
        cnt ≤ cnt' ∧
        ConsistentS o.vm V' env2 ∧
        (∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') ∧
        OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧
        envReadU64 env2 nm = some (SExpr.evalBV (envReader env) e) := by
  intro Γ vm V env cnt o nm cnt' hc hclean hlow
  have h := lowerSExpr_denoteWith defaultLeaf e vm V env cnt o nm cnt' hc hclean hlow
  rwa [catCryptDenoteWith_default] at h

/-- **Front-general scalar preservation at a leaf oracle** (`translateDialectFull`
    form). For every leaf oracle `ls` and any straight-line covered body `c`, the
    emitted `Com`-prefix `o.cont`, denoted under `catCryptDenoteWith ls`, denotes
    exactly the body's `semScalarL ls` semantics: an extended valuation `V'`
    consistent with the final `VarMap` and the `semScalarL ls`-updated env, on which
    every tail's denotation through `o.cont` (at the entry `V`) equals the tail's
    denotation at `V'`. Induction on the coverage; `rSeq` via `ComCont.comp`; each
    leaf arm binds `ls` at the argument values, which agree with the environment's
    under `ConsistentS` (`argVals_of_resolve`). -/
theorem translateDialectFull_denoteWith (ls : SemLeafSpec) {c : LowCT} (hcov : IsCoveredS c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectFull vm c = some o →
      semScalarL ls c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  induction hcov with
  | rSkip =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull, translateDialect] at htr
      simp only [semScalarL] at hsem
      obtain rfl := Option.some.inj hsem
      obtain rfl := Option.some.inj htr
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | rAssert label =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      simp only [semScalarL] at hsem
      obtain rfl := Option.some.inj hsem
      obtain rfl := Option.some.inj htr
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | @rBlock body hbody ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      simp only [semScalarL] at hsem
      exact ih vm V env env' o hc htr hsem
  | @rSeq c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      intro Γ vm V env env' o hc htr hsem
      rcases ht1 : translateDialectFull vm c₁ with _ | o₁
      · simp [translateDialectFull, ht1] at htr
      · rcases ht2 : translateDialectFull o₁.vm c₂ with _ | o₂
        · simp [translateDialectFull, ht1, ht2] at htr
        · rcases hs1 : semScalarL ls c₁ env with _ | env₁
          · simp [semScalarL, hs1] at hsem
          · simp only [semScalarL, hs1, Option.bind_some] at hsem
            simp only [translateDialectFull, ht1, ht2, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨V₁, hc₁, hcont₁⟩ := ih₁ vm V env env₁ o₁ hc ht1 hs1
            obtain ⟨V₂, hc₂, hcont₂⟩ := ih₂ o₁.vm V₁ env₁ env' o₂ hc₁ ht2 hsem
            refine ⟨V₂, hc₂, ?_⟩
            intro t tail
            obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
            obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp o₁.cont o₂.cont tail = some com
              simp only [ComCont.comp, hcom₂, hcom]
            · rw [hden, hden₂]
  | rScalarSet name n =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull, translateDialect] at htr
      obtain rfl := Option.some.inj htr
      simp only [semScalarL] at hsem
      obtain rfl := Option.some.inj hsem
      obtain ⟨hcons, hcont⟩ :=
        scalar_stepWith ls vm V env hc name
          ({ op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil } :
            Expr catCryptDialect Γ (.sword 64))
      exact ⟨_, hcons, fun tail => hcont tail⟩
  | @rLetU64Zero name body hbody ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      rcases htb : translateDialectFull (vm.bind name) body with _ | ob
      · rw [htb] at htr; simp at htr
      · rw [htb] at htr
        simp only [Option.some.injEq] at htr
        obtain rfl := htr
        obtain ⟨hcons0, hcont0⟩ :=
          scalar_stepWith ls vm V env hc name
            ({ op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil } :
              Expr catCryptDialect Γ (.sword 64))
        simp only [semScalarL] at hsem
        obtain ⟨V', hc', hcont1⟩ :=
          ih (vm.bind name) (V.extend _) _ env' ob hcons0 htb hsem
        refine ⟨V', hc', ?_⟩
        intro t tail
        obtain ⟨com1, hcom1, hden1⟩ := hcont1 tail
        obtain ⟨com, hcom, hden⟩ := hcont0 com1
        refine ⟨com, ?_, ?_⟩
        · show ComCont.comp (ComCont.varBind _) ob.cont tail = some com
          simp only [ComCont.comp, hcom1, hcom]
        · rw [hden, hden1]
  | rCall fname dst args =>
      intro Γ vm V env env' o hc htr hsem
      rcases hra : resolveLocatedArgs vm args with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        simp only [semScalarL] at hsem
        obtain rfl := Option.some.inj hsem
        obtain ⟨hcons, hcont⟩ :=
          scalar_stepWith ls vm V env hc dst.locVar
            (extCallExpr fname (encodeTy dst.locDst) (listSigmaToCHVector resolvedArgs).snd)
        rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
        exact ⟨_, hcons, fun tail => hcont tail⟩
  | rSelect dst sel src0 src1 =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      split at htr
      · rename_i sV aV cV hd hs ha hcv
        obtain rfl := Option.some.inj htr
        have henvS : env sel = some ⟨.sword 64, (toVIRVar sV).lookup V⟩ := by
          rw [← hc sel, hs]; rfl
        have henvA : env src0.locVar = some ⟨.sword 64, (toVIRVar aV).lookup V⟩ := by
          rw [← hc src0.locVar, ha]; rfl
        have henvC : env src1.locVar = some ⟨.sword 64, (toVIRVar cV).lookup V⟩ := by
          rw [← hc src1.locVar, hcv]; rfl
        simp only [semScalarL, hd, henvS, henvA, henvC] at hsem
        obtain rfl := Option.some.inj hsem
        exact selectCmpCont_denoteWith ls vm V env hc dst.locVar sV aV cV
      · rename_i hnot
        rcases hra : resolveLocatedArgs vm [{ locVar := sel, locSrc := .TU64 }, src0, src1]
          with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          have hsem' : semScalarL ls (.RSelect dst sel src0 src1) env =
              some (env.upd dst.locVar (t := encodeTy dst.locDst)
                (ls "select" (encodeTy dst.locDst)
                  (argVals env (locNames [{ locVar := sel, locSrc := .TU64 }, src0, src1])))) := by
            simp only [semScalarL]
            split
            · rename_i s a c hd hs ha hcv
              obtain ⟨sV, hs'⟩ := consistentS_bound hc hs
              obtain ⟨aV, ha'⟩ := consistentS_bound hc ha
              obtain ⟨cV, hcv'⟩ := consistentS_bound hc hcv
              exact (hnot sV aV cV hd hs' ha' hcv').elim
            · rfl
          rw [hsem'] at hsem
          obtain rfl := Option.some.inj hsem
          obtain ⟨hcons, hcont⟩ :=
            scalar_stepWith ls vm V env hc dst.locVar
              (extCallExpr "select" (encodeTy dst.locDst) (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
          exact ⟨_, hcons, fun tail => hcont tail⟩
  | rCallDstThreaded fname dst args =>
      intro Γ vm V env env' o hc htr hsem
      rcases hra : resolveLocatedArgs vm (dst :: args) with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        simp only [semScalarL] at hsem
        obtain rfl := Option.some.inj hsem
        obtain ⟨hcons, hcont⟩ :=
          scalar_stepWith ls vm V env hc dst.locVar
            (extCallExpr fname (encodeTy dst.locDst) (listSigmaToCHVector resolvedArgs).snd)
        rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
        exact ⟨_, hcons, fun tail => hcont tail⟩
  | rTupleLoad dst src idx =>
      intro Γ vm V env env' o hc htr hsem
      rcases hra : resolveLocatedArgs vm [src] with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        simp only [semScalarL] at hsem
        obtain rfl := Option.some.inj hsem
        obtain ⟨hcons, hcont⟩ :=
          scalar_stepWith ls vm V env hc dst.locVar
            (extCallExpr ("tupleLoad:" ++ toString idx) (encodeTy dst.locDst)
              (listSigmaToCHVector resolvedArgs).snd)
        rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
        exact ⟨_, hcons, fun tail => hcont tail⟩
  | rArrLoadLit dst src idx =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      split at htr
      · rename_i k n arrV hd hsrc hs
        obtain rfl := Option.some.inj htr
        have henv : env src.locVar = some ⟨.memref n, (toVIRVar arrV).lookup V⟩ := by
          rw [← hc src.locVar, hs]; rfl
        simp only [semScalarL, hd, hsrc, henv] at hsem
        obtain rfl := Option.some.inj hsem
        let eIdx : Expr catCryptDialect Γ (.sword 64) :=
          { op := .bvConst 64 (BitVec.ofNat 64 idx), retTy_eq := rfl, args := .nil }
        have hcw := consistentS_weaken vm V env hc (eIdx.denote V)
        obtain ⟨_, hcont1⟩ := scalar_stepWith ls vm V env hc dst.locVar eIdx
        obtain ⟨hcons2, hcont2⟩ :=
          scalar_stepWith ls vm.weaken (V.extend _) env hcw dst.locVar
            ({ op := .memrefGetDyn n, retTy_eq := rfl,
               args := .cons (toVIRVar (CVar.there arrV))
                 (.cons (toVIRVar (CVar.here : CVar (.sword 64 :: Γ) (.sword 64))) .nil) } :
              Expr catCryptDialect (.sword 64 :: Γ) (.sword 64))
        refine ⟨_, hcons2, ?_⟩
        intro t tail
        obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
        obtain ⟨com, hcom, hden⟩ := hcont1 com2
        refine ⟨com, ?_, ?_⟩
        · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
          simp only [ComCont.comp, hcom2]
          exact hcom
        · exact hden.trans hden2
      · rename_i hnot
        rcases hra : resolveLocatedArgs vm [src] with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          have hsem' : semScalarL ls (.RArrLoadLit dst src idx) env =
              some (env.upd dst.locVar (t := encodeTy dst.locDst)
                (ls ("arrLoad:" ++ toString idx) (encodeTy dst.locDst)
                  (argVals env (locNames [src])))) := by
            simp only [semScalarL]
            split
            · rename_i k n arr hd hsrc hs
              obtain ⟨arrV, hs'⟩ := consistentS_bound hc hs
              exact (hnot k n arrV hd hsrc hs').elim
            · rfl
          rw [hsem'] at hsem
          obtain rfl := Option.some.inj hsem
          obtain ⟨hcons, hcont⟩ :=
            scalar_stepWith ls vm V env hc dst.locVar
              (extCallExpr ("arrLoad:" ++ toString idx) (encodeTy dst.locDst)
                (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
          exact ⟨_, hcons, fun tail => hcont tail⟩
  | rArrStoreLit arr idx src =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      split at htr
      · rename_i k n arrV srcV harr ha hs
        obtain rfl := Option.some.inj htr
        have henvA : env arr.locVar = some ⟨.memref n, (toVIRVar arrV).lookup V⟩ := by
          rw [← hc arr.locVar, ha]; rfl
        have henvS : env src.locVar = some ⟨.sword 64, (toVIRVar srcV).lookup V⟩ := by
          rw [← hc src.locVar, hs]; rfl
        simp only [semScalarL, harr, henvA, henvS] at hsem
        obtain rfl := Option.some.inj hsem
        let eIdx : Expr catCryptDialect Γ (.sword 64) :=
          { op := .bvConst 64 (BitVec.ofNat 64 idx), retTy_eq := rfl, args := .nil }
        have hcw := consistentS_weaken vm V env hc (eIdx.denote V)
        obtain ⟨_, hcont1⟩ := scalar_stepWith ls vm V env hc arr.locVar eIdx
        obtain ⟨hcons2, hcont2⟩ :=
          scalar_stepWith ls vm.weaken (V.extend _) env hcw arr.locVar
            ({ op := .memrefSetDyn n, retTy_eq := rfl,
               args := .cons (toVIRVar (CVar.there arrV))
                 (.cons (toVIRVar (CVar.here : CVar (.sword 64 :: Γ) (.sword 64)))
                   (.cons (toVIRVar (CVar.there srcV)) .nil)) } :
              Expr catCryptDialect (.sword 64 :: Γ) (.memref n))
        refine ⟨_, hcons2, ?_⟩
        intro t tail
        obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
        obtain ⟨com, hcom, hden⟩ := hcont1 com2
        refine ⟨com, ?_, ?_⟩
        · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
          simp only [ComCont.comp, hcom2]
          exact hcom
        · exact hden.trans hden2
      · rename_i hnot
        rcases hra : resolveLocatedArgs vm [arr, src] with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          have hsem' : semScalarL ls (.RArrStoreLit arr idx src) env =
              some (env.upd arr.locVar (t := encodeTy arr.locDst)
                (ls ("arrStore:" ++ toString idx) (encodeTy arr.locDst)
                  (argVals env (locNames [arr, src])))) := by
            simp only [semScalarL]
            split
            · rename_i k n a v harr ha hs
              obtain ⟨arrV, ha'⟩ := consistentS_bound hc ha
              obtain ⟨srcV, hs'⟩ := consistentS_bound hc hs
              exact (hnot k n arrV srcV harr ha' hs').elim
            · rfl
          rw [hsem'] at hsem
          obtain rfl := Option.some.inj hsem
          obtain ⟨hcons, hcont⟩ :=
            scalar_stepWith ls vm V env hc arr.locVar
              (extCallExpr ("arrStore:" ++ toString idx) (encodeTy arr.locDst)
                (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons hcont
          exact ⟨_, hcons, fun tail => hcont tail⟩
  | rCallSwap fname dest1 dest2 args =>
      intro Γ vm V env env' o hc htr hsem
      rcases hra : resolveLocatedArgs vm args with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        rcases hra2 : resolveLocatedArgs (vm.bind dest1.locVar) args with _ | resolvedArgs2
        · rw [hra2] at htr; simp at htr
        · rw [hra2] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          simp only [semScalarL] at hsem
          obtain rfl := Option.some.inj hsem
          obtain ⟨hcons1, hcont1⟩ :=
            scalar_stepWith ls vm V env hc dest1.locVar
              (extCallExpr fname (encodeTy dest1.locDst) (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hc _ resolvedArgs hra] at hcons1 hcont1
          obtain ⟨hcons2, hcont2⟩ :=
            scalar_stepWith ls (vm.bind dest1.locVar) (V.extend _) _ hcons1 dest2.locVar
              (extCallExpr fname (encodeTy dest2.locDst) (listSigmaToCHVector resolvedArgs2).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hcons1 _ resolvedArgs2 hra2]
            at hcons2 hcont2
          refine ⟨_, hcons2, ?_⟩
          intro t tail
          obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
          obtain ⟨com, hcom, hden⟩ := hcont1 com2
          refine ⟨com, ?_, ?_⟩
          · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
            simp only [ComCont.comp, hcom2, hcom]
          · exact hden.trans hden2
  | rCloneCall cv tt oldDest innerF newDest args =>
      intro Γ vm V env env' o hc htr hsem
      rcases hlk : vm.lookup oldDest.locVar with _ | ⟨cloneTy, oldVar⟩
      · simp [translateDialectFull, hlk] at htr
      · simp only [translateDialectFull, hlk] at htr
        rcases hra : resolveLocatedArgs (vm.bind cv) args with _ | resolvedArgs
        · rw [hra] at htr; simp at htr
        · rw [hra] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          have henv : env oldDest.locVar = some ⟨cloneTy, (toVIRVar oldVar).lookup V⟩ := by
            rw [← hc oldDest.locVar, hlk]; rfl
          simp only [semScalarL, henv] at hsem
          obtain rfl := Option.some.inj hsem
          obtain ⟨hcons1, hcont1⟩ :=
            scalar_stepWith ls vm V env hc cv
              (extCallExpr "clone" cloneTy (.cons oldVar .nil))
          rw [extCallExpr_denoteWith] at hcons1 hcont1
          obtain ⟨hcons2, hcont2⟩ :=
            scalar_stepWith ls (vm.bind cv) (V.extend _) _ hcons1 newDest.locVar
              (extCallExpr innerF (encodeTy newDest.locDst) (listSigmaToCHVector resolvedArgs).snd)
          rw [extCallExpr_denoteWith, argVals_of_resolve hcons1 _ resolvedArgs hra]
            at hcons2 hcont2
          refine ⟨_, hcons2, ?_⟩
          intro t tail
          obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
          obtain ⟨com, hcom, hden⟩ := hcont1 com2
          refine ⟨com, ?_, ?_⟩
          · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
            simp only [ComCont.comp, hcom2, hcom]
          · exact hden.trans hden2
  | rLimbStore loc idx v =>
      intro Γ vm V env env' o hc htr hsem
      rcases hlk : vm.lookup loc.locVar with _ | ⟨mt, arr⟩
      · have henv : env loc.locVar = none := by rw [← hc loc.locVar, hlk]; rfl
        simp only [translateDialectFull, hlk] at htr
        simp only [semScalarL, henv] at hsem
        rcases hen : encodeTy loc.locDst with _ | _ | _ | _ | _ | n
        all_goals (rw [hen] at htr hsem; dsimp only at htr hsem)
        case memrefW => exact absurd htr (by simp)
        iterate 5 (exact absurd htr (by simp))
        by_cases hlt : idx < n
        · rw [if_pos hlt] at htr hsem
          simp only [Option.some.injEq] at htr hsem
          obtain rfl := htr
          obtain rfl := hsem
          have hcw := consistentS_weaken vm V env hc
            (({ op := .bvConst 64 v, retTy_eq := rfl, args := .nil } :
              Expr catCryptDialect Γ (.sword 64)).denote V)
          obtain ⟨_, hcont1⟩ :=
            scalar_stepWith ls vm V env hc loc.locVar
              ({ op := .bvConst 64 v, retTy_eq := rfl, args := .nil } :
                Expr catCryptDialect Γ (.sword 64))
          obtain ⟨hcons2, hcont2⟩ :=
            scalar_stepWith ls vm.weaken (V.extend _) env hcw loc.locVar (limbLitExpr idx n)
          refine ⟨_, hcons2, ?_⟩
          intro t tail
          obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
          obtain ⟨com, hcom, hden⟩ := hcont1 com2
          refine ⟨com, ?_, ?_⟩
          · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
            simp only [ComCont.comp, hcom2, hcom]
          · exact hden.trans hden2
        · rw [if_neg hlt] at htr; simp at htr
      · rcases mt with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | n
        case memrefW => simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp only [translateDialectFull, hlk] at htr
          by_cases hlt : idx < n
          · rw [dif_pos hlt] at htr
            simp only [Option.some.injEq] at htr
            obtain rfl := htr
            have henv : env loc.locVar = some ⟨.memref n, (toVIRVar arr).lookup V⟩ := by
              rw [← hc loc.locVar, hlk]; rfl
            simp only [semScalarL, henv, dif_pos hlt] at hsem
            obtain rfl := Option.some.inj hsem
            have hcw := consistentS_weaken vm V env hc
              (({ op := .bvConst 64 v, retTy_eq := rfl, args := .nil } :
                Expr catCryptDialect Γ (.sword 64)).denote V)
            obtain ⟨_, hcont1⟩ :=
              scalar_stepWith ls vm V env hc loc.locVar
                ({ op := .bvConst 64 v, retTy_eq := rfl, args := .nil } :
                  Expr catCryptDialect Γ (.sword 64))
            obtain ⟨hcons2, hcont2⟩ :=
              scalar_stepWith ls vm.weaken (V.extend _) env hcw loc.locVar
                ({ op := .memrefSet n ⟨idx, hlt⟩, retTy_eq := rfl,
                   args := .cons (toVIRVar (CVar.there arr)) (.cons (toVIRVar CVar.here) .nil) } :
                  Expr catCryptDialect (.sword 64 :: Γ) (.memref n))
            refine ⟨_, hcons2, ?_⟩
            intro t tail
            obtain ⟨com2, hcom2, hden2⟩ := hcont2 tail
            obtain ⟨com, hcom, hden⟩ := hcont1 com2
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp (ComCont.varBind _) (ComCont.varBind _) tail = some com
              simp only [ComCont.comp, hcom2, hcom]
            · exact hden.trans hden2
          · rw [dif_neg hlt] at htr; simp at htr
  | rCallN fname dests args =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectFull] at htr
      simp only [semScalarL] at hsem
      obtain rfl := Option.some.inj hsem
      exact loopCallNDestsD_denoteWith ls fname args dests vm V env o hc htr
  | rArrLoad dst src idxVar =>
      intro Γ vm V env env' o hc htr hsem
      rcases hsrc : vm.lookup src.locVar with _ | σ_src
      · simp [translateDialectFull, resolveLocatedArgs, hsrc] at htr
      · rcases hidx : vm.lookup idxVar with _ | idxSig
        · simp [translateDialectFull, resolveLocatedArgs, hsrc, hidx] at htr
        · simp only [translateDialectFull, resolveLocatedArgs, hsrc, hidx] at htr
          obtain rfl := (Option.some.inj htr).symm
          rcases σ_src with ⟨st, sv⟩
          rcases idxSig with ⟨it, iv⟩
          set hv := (listSigmaToCHVector ([(⟨st, sv⟩ : (t : CryptoTy) × CVar Γ t)] ++
            [(⟨it, iv⟩ : (t : CryptoTy) × CVar Γ t)])).snd with hhv
          have henvs : env src.locVar = some ⟨st, (toVIRVar sv).lookup V⟩ := by
            rw [← hc src.locVar, hsrc]; rfl
          have henvi : env idxVar = some ⟨it, (toVIRVar iv).lookup V⟩ := by
            rw [← hc idxVar, hidx]; rfl
          have hargs : hvecSigmaList (Expr.lookupArgs (toVIRArgs hv) V)
              = argVals env (locNames [src] ++ [idxVar]) := by
            rw [hhv, hvecSigmaList_listSigma]
            simp [argVals, locNames, henvs, henvi]
          have hval : env' = env.upd dst.locVar (t := encodeTy dst.locDst)
              (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _
                (arrLoadExpr dst.locDst [⟨st, sv⟩] ⟨it, iv⟩ hv) V) := by
            have h2 : some env' = some (env.upd dst.locVar (t := encodeTy dst.locDst)
                (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _
                  (arrLoadExpr dst.locDst [⟨st, sv⟩] ⟨it, iv⟩ hv) V)) := by
              rw [← hsem]
              simp only [semScalarL, henvs, henvi]
              cases dst.locDst
              case TU64 =>
                rcases st with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | nmem <;>
                  rcases it with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | w | _ <;>
                  first
                  | (simp [arrLoadExpr, extCallExpr_denoteWith, hargs]; done)
                  | (rcases eq_or_ne w 64 with rfl | hw <;>
                      first
                      | rfl
                      | simp_all [arrLoadExpr, extCallExpr_denoteWith, CryptoTy.sword.injEq])
              all_goals
                simp [arrLoadExpr, extCallExpr_denoteWith, hargs]
            exact Option.some.inj h2
          subst hval
          obtain ⟨hcons, hcont⟩ :=
            scalar_stepWith ls vm V env hc dst.locVar
              (arrLoadExpr dst.locDst [⟨st, sv⟩] ⟨it, iv⟩ hv)
          refine ⟨_, hcons, ?_⟩
          intro t tail
          simp only [arrLoadCont_eq]
          exact hcont tail
  | rArrStore arr idxVar src =>
      intro Γ vm V env env' o hc htr hsem
      rcases harr : vm.lookup arr.locVar with _ | σ_arr
      · simp [translateDialectFull, resolveLocatedArgs, harr] at htr
      · rcases hsrc : vm.lookup src.locVar with _ | σ_src
        · simp [translateDialectFull, resolveLocatedArgs, harr, hsrc] at htr
        · rcases hidx : vm.lookup idxVar with _ | idxSig
          · simp [translateDialectFull, resolveLocatedArgs, harr, hsrc, hidx] at htr
          · simp only [translateDialectFull, resolveLocatedArgs, harr, hsrc, hidx] at htr
            obtain rfl := (Option.some.inj htr).symm
            rcases σ_arr with ⟨at_, av⟩
            rcases σ_src with ⟨stt, sv⟩
            rcases idxSig with ⟨it, iv⟩
            set hv := (listSigmaToCHVector
              ([(⟨at_, av⟩ : (t : CryptoTy) × CVar Γ t),
                (⟨stt, sv⟩ : (t : CryptoTy) × CVar Γ t)] ++
               [(⟨it, iv⟩ : (t : CryptoTy) × CVar Γ t)])).snd with hhv
            have henva : env arr.locVar = some ⟨at_, (toVIRVar av).lookup V⟩ := by
              rw [← hc arr.locVar, harr]; rfl
            have henvs : env src.locVar = some ⟨stt, (toVIRVar sv).lookup V⟩ := by
              rw [← hc src.locVar, hsrc]; rfl
            have henvi : env idxVar = some ⟨it, (toVIRVar iv).lookup V⟩ := by
              rw [← hc idxVar, hidx]; rfl
            have hargs : hvecSigmaList (Expr.lookupArgs (toVIRArgs hv) V)
                = argVals env (locNames [arr, src] ++ [idxVar]) := by
              rw [hhv, hvecSigmaList_listSigma]
              simp [argVals, locNames, henva, henvs, henvi]
            have hval : env' = env.upd arr.locVar (t := encodeTy arr.locDst)
                (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _
                  (arrStoreExpr arr.locDst [⟨at_, av⟩, ⟨stt, sv⟩] ⟨it, iv⟩ hv) V) := by
              have h2 : some env' = some (env.upd arr.locVar (t := encodeTy arr.locDst)
                  (@Expr.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _
                    (arrStoreExpr arr.locDst [⟨at_, av⟩, ⟨stt, sv⟩] ⟨it, iv⟩ hv) V)) := by
                rw [← hsem]
                simp only [semScalarL, henva, henvs, henvi]
                rcases at_ with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | n <;>
                  rcases stt with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ws | _ <;>
                  rcases it with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | wi | _ <;>
                  first
                  | (simp [arrStoreExpr, extCallExpr_denoteWith, hargs]; done)
                  | (rcases eq_or_ne ws 64 with rfl | hws
                     · first
                       | (simp [arrStoreExpr]; done)
                       | (rcases eq_or_ne wi 64 with rfl | hwi
                          · simp only [arrStoreExpr]
                            by_cases hmem : encodeTy arr.locDst = .memref n
                            · simp only [dif_pos hmem, expr_denote_castWith]
                              rfl
                            · simp only [dif_neg hmem, extCallExpr_denoteWith, hargs]
                          · simp_all [arrStoreExpr, extCallExpr_denoteWith, CryptoTy.sword.injEq])
                     · simp_all [arrStoreExpr, extCallExpr_denoteWith, CryptoTy.sword.injEq])
              exact Option.some.inj h2
            subst hval
            obtain ⟨hcons, hcont⟩ :=
              scalar_stepWith ls vm V env hc arr.locVar
                (arrStoreExpr arr.locDst [⟨at_, av⟩, ⟨stt, sv⟩] ⟨it, iv⟩ hv)
            refine ⟨_, hcons, ?_⟩
            intro t tail
            simp only [arrStoreCont_eq]
            exact hcont tail
  | rScalarSetExpr x e hclean =>
      intro Γ vm V env env' o hc htr hsem
      rcases hlow : TranslateDialectDirectArms.lowerSExpr vm 0 e with _ | r
      · simp [translateDialectFull, hlow] at htr
      · obtain ⟨oe, nme, cnte'⟩ := r
        rcases hlk : TranslateDialectDirectArms.lookupU64 oe.vm nme with _ | v
        · simp [translateDialectFull, hlow, hlk] at htr
        · simp only [translateDialectFull, hlow, hlk] at htr
          obtain rfl := Option.some.inj htr
          obtain ⟨Ve, env2, hsemLow, hle0, hce, hconte, hotbe, hroke, hvale⟩ :=
            lowerSExpr_denoteWith ls e vm V env 0 oe nme cnte' hc hclean hlow
          simp only [semScalarL, hsemLow] at hsem
          obtain rfl := Option.some.inj hsem
          have hvv : (toVIRVar v).lookup Ve = SExpr.evalBV (envReader env) e := by
            have hr := consistentS_readU64 hce nme hlk
            exact Option.some.inj (hr.symm.trans hvale)
          set copyE : Expr catCryptDialect oe.Γ' (.sword 64) :=
            { op := .bvShiftL 64 0, retTy_eq := rfl, args := .cons (toVIRVar v) .nil } with hcopyE
          have hcopy : copyE.denote Ve = SExpr.evalBV (envReader env) e := by
            rw [hcopyE, ← hvv]; exact BitVec.shiftLeft_zero _
          obtain ⟨hcons, hcont⟩ := scalar_stepWith ls oe.vm Ve env2 hce x copyE
          refine ⟨Ve.extend (copyE.denote Ve), ?_, ?_⟩
          · have hee : env2.upd x (t := .sword 64) (copyE.denote Ve)
                = env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e) := by rw [hcopy]
            rw [← hee]; exact hcons
          · intro t tail
            obtain ⟨comV, hcomV, hdenV⟩ := hcont tail
            obtain ⟨comA, hcomA, hdenA⟩ := hconte comV
            refine ⟨comA, ?_, ?_⟩
            · show ComCont.comp oe.cont (ComCont.varBind copyE) tail = some comA
              simp only [ComCont.comp, hcomV, hcomA]
            · rw [hdenA]; exact hdenV

/-- **Front-general scalar preservation** (`translateDialectFull` form). For any
    straight-line covered body `c`, the emitted `Com`-prefix `o.cont` denotes
    exactly the body's `semScalar` semantics: an extended valuation `V'`
    consistent with the final `VarMap` and the `semScalar`-updated env, on which
    every tail's denotation through `o.cont` (at the entry `V`) equals the tail's
    denotation at `V'`. The instance of `translateDialectFull_denoteWith` at
    `defaultLeaf`. -/
theorem translateDialectFull_denote {c : LowCT} (hcov : IsCoveredS c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectFull vm c = some o →
      semScalar c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [semScalar_eq_semScalarL] at hsem
  have h := translateDialectFull_denoteWith defaultLeaf hcov vm V env env' o hc htr hsem
  rwa [catCryptDenoteWith_default] at h

/-- **Front-general scalar preservation at a leaf oracle** (`translateDialectControl`
    form). On the straight-line covered fragment `translateDialectControl` coincides
    with `translateDialectFull`, so `translateDialectFull_denoteWith` transfers. -/
theorem translateDialectControl_denoteWith (ls : SemLeafSpec) {c : LowCT}
    (hcov : IsCoveredS c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm c = some o →
      semScalarL ls c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  intro Γ vm V env env' o hc htr hsem
  have hfull : translateDialectControl vm c = translateDialectFull vm c :=
    translateDialectControl_eq_full_of_covered vm hcov.toIsCovered
  rw [hfull] at htr
  exact translateDialectFull_denoteWith ls hcov vm V env env' o hc htr hsem

/-- **Front-general scalar preservation** (`translateDialectControl` form, the
    spec-named entry point). On the straight-line covered fragment
    `translateDialectControl` coincides with `translateDialectFull` (it delegates
    every non-`RFor`/`RIfNz`/`RWhileNz` arm there), so the homomorphism transfers
    verbatim. This is the scalar analogue of
    `TranslateDialectVsimdDenote.translateDialectControlV_denote`; adding the
    `RScalarSetExpr` induction case (and then `RFor` / `RIfNz`) grows the covered
    fragment toward the full `IsCoveredCtl`. -/
theorem translateDialectControl_denote {c : LowCT} (hcov : IsCoveredS c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm c = some o →
      semScalar c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  have hfull : translateDialectControl vm c = translateDialectFull vm c :=
    translateDialectControl_eq_full_of_covered vm hcov.toIsCovered
  rw [hfull] at htr
  exact translateDialectFull_denote hcov vm V env env' o hc htr hsem

/-! ## 7. Mechanical straight-line arms closed; outstanding obligation (scalar-`SExpr`)

The whole mechanical straight-line fragment is proved. Beyond the composition
arms (`RSeq`/`RBlock`/`RSkip`), three shapes of arm close uniformly:

* **Single-binding opaque leaf** (`RCall`, `RCallDstThreaded`, `RTupleLoad`, and
  `RSelect`/`RArrLoadLit`/`RArrStoreLit` on slots outside their word shapes) and
  single concrete bind (`RScalarSet`, a `bvConst`): one `ComCont.varBind` closed
  directly by `scalar_step`; the emitted `extCallExpr`/`bvConst` denotes to the
  same waist (`CryptoTy.default` / the literal) `semScalar` binds, so the `exact`
  closes by definitional agreement.
* **Multi-binding folds** (`RLetU64Zero` = prefix bind + body IH; `RCallSwap` /
  `RCloneCall` = two binds; `RLimbStore` and the word-shape `RArrLoadLit` /
  `RArrStoreLit` = a weaken-step + one bind; the word-shape `RSelect` = two
  weaken-steps + one bind, `selectCmpCont_denote`; `RCallN` = N binds by induction
  on the dest list, generalizing the context): each per-bind step is a `scalar_step`
  (or `consistentS_weaken` for an anonymous temp), composed via `ComCont.comp` along
  the `RSeq` spine.

The dynamic-index **load** and **store** arms (`RArrLoad`, `RArrStore`) are
proved cases of the homomorphism (§5b/§5c + the `rArrLoad`/`rArrStore` arms of
`translateDialectFull_denote`). Their front combinators `arrLoadCont` /
`arrStoreCont` refactor as `ComCont.varBind (arrLoadExpr …)` /
`ComCont.varBind (arrStoreExpr …)` (`arrLoadCont_eq` / `arrStoreCont_eq`), and
the induction cases reduce the front's literal-pattern dependent match in
**lock-step** with `semScalar`'s matching arm by casing the shape discriminants
(`rcases` the slot `CryptoTy`s — which *substitute* rather than leaving the HEq
equations `split` produces — and `eq_or_ne _ 64` width splits), each case closing
by `scalar_step` exactly as `RCall`. The reusable lesson: **case the discriminants
(so both mirrored matches ι-reduce together); do not `split` them** (`split`
reduces only one match and leaves the other under an unusable negation/HEq
hypothesis).

The **store** arm's extra wrinkle — `arrStoreCont`'s memref branch wraps its
`memrefSetDyn` `varBind` in a `ComCont.castCtx` (a codomain transport guarded by
`encodeTy arr.locDst = .memref n`), and `semScalar`'s value carries a matching
`h ▸` — is discharged by two *general* congruence lemmas, `castCtx_varBind`
(`castCtx (congrArg (·::Γ) hh) (varBind e) = varBind (hh ▸ e)`) and
`expr_denote_cast` (`(hh ▸ e).denote V = hh ▸ (e.denote V)`), each a single
`cases hh` with NO case explosion. Crucially the array's declared encoding
`encodeTy arr.locDst` is kept **opaque**: instead of the 20-way `cases
arr.locDst` (which combined with the slot `rcases` + width splits would exceed
the `whnf` budget), a single `by_cases encodeTy arr.locDst = .memref n` drives
both `semScalar`'s guard and `arrStoreExpr`'s guard together — the parametric
per-op congruence factoring that avoids the case product entirely.

The **`RScalarSetExpr x e`** arm (the point-op brick route) is proved over
its `srcClean` fragment. The front lowers the `SExpr` tree via `lowerSExpr` into a
**chain** of `ComCont.varBind`s over fresh `__sx` temporaries (not a single
`varBind`), so beyond `scalar_step` it needs the `SExpr`-recursion homomorphism
`lowerSExpr_denote` (§5f): an env-level word-op mirror `semLowerSExpr` threading
the same fresh temporaries, proved by induction on `SExpr` to match the emitted
chain's denotation via `ComCont.comp`, with its result slot resolving to the
closed-form `SExpr.evalBV (envReader env) e`. The three sub-obligations:

1. **`SExpr`-recursion homomorphism** — the induction body of `lowerSExpr_denote`;
   each binary node is a fresh `varBind` over the two sub-chains (`ComCont.comp`),
   its value tied through `consistentS_readU64` + the reader congruence
   `evalBV_congr`.
2. **Fresh-temp non-collision** — `tmpName` injectivity (§2b, proved from a
   decimal-digit left inverse `toDigits_val`, absent from core/Mathlib) plus the
   `OnlyTmpBelow` / `ResultOK` bookkeeping (`readU64_stable`, `onlyTmpBelow_*`):
   temps `tmpName k` never collide with a `srcClean` source read, and a later
   fresh temp never overwrites an earlier result name.
3. **Shift-arm reconciliation** — the front's inline amount-shape match (the
   immediate op `bvShiftL 64 k` on a literal amount `SLit k`, the variable
   `bvShiftLV 64` otherwise) is cased by a 2-way `split`, and the literal branch
   reconciles `k = (BitVec.ofNat 64 k).toNat` from `srcClean`'s `k < 2^64`
   literal bound — so `SShl`/`SShr` (the Keccak-f1600 round-body and secp256k1
   `feMul`-brick alphabet) are covered, as is the `SMulHiU` high-multiply via the
   `mulHiC`↔`sexprMulHiU` bridge. Only the signed `SAsr`/`SMulS`/`SMulHiS` (plus
   `SLt`/`SLimb`) stay outside `srcClean`.

The per-brick *field* correctness (that a brick computes `(a·b) mod p`) is the
separate deep obligation recorded in `Secp256k1PointOpCompositional`. -/

/-! ## 8. Stage 2 — the control arms (`RFor` / `RIfNz`)

The control-flow extension of the preservation homomorphism, from the
straight-line `IsCoveredS` to the full control-extended fragment (the scalar
twin of `TranslateDialectDirectControl.IsCoveredCtl`). Three layers:

* **coverage** — `IsCoveredSCtl` mirrors `IsCoveredCtl` arm-for-arm
  (`ofCovered`/`rFor`/`rIfNz`), with `IsCoveredS`'s `srcClean` side condition on
  `RScalarSetExpr` in place of `IsCovered`'s unconditional arm;
* **the extension/inertness invariant** (`translateDialectControl_ext`) — every
  accepted translation's output context is `Δ ++ Γ` for some pushed prefix `Δ`,
  and a context-invariant translation (`Δ = []`) is env-INERT (`semScalar` is
  the identity on it). This is the fact `RIfNz`'s (A)/(B) cases rest on: there
  the front passes through ONE branch's prefix and discards the
  other, the discarded branch is exactly the context-invariant one, and
  inertness makes the sequential waist semantics agree with the single-branch
  denotation. Proved over ALL of `LowCT` (no coverage hypothesis) by structural
  induction, with per-chain auxiliaries for `lowerSExpr` / `loopCallNDestsD` /
  `loopRForD`;
* **the two induction cases** — `RFor` by `Nat`-induction over the meta-unroll
  (`loopRForD_denote`: each trip is a `scalar_step` counter bind composed with
  the body IH via `ComCont.comp`, the `RCallN` fold pattern with the body IH in
  place of the opaque bind), `RIfNz` by the front's four-way case split
  ((A)/(B1)/(B2) via branch IH + inertness; (C′) via five `consistentS_weaken`
  steps + one `scalar_step` on the φ-merge `ite`, cased on the scrutinee). -/

/-- The control-extended scalar-covered `LowCT` fragment: the straight-line
    covered arms plus `RFor` over covered bodies, `RIfNz` over covered
    branches, the binders `RLetU64Zero` / `RLetZero` over covered bodies and
    `RSeq` of two covered commands — the shape of
    `TranslateDialectDirectControl.IsCoveredCtl` without its `rWhileNz` arm. -/
inductive IsCoveredSCtl : LowCT → Prop
  | ofStraight {c : LowCT} : IsCoveredS c → IsCoveredSCtl c
  | rSeq {c₁ c₂ : LowCT} : IsCoveredSCtl c₁ → IsCoveredSCtl c₂ → IsCoveredSCtl (.RSeq c₁ c₂)
  | rFor {x : String} {N : Nat} {body : LowCT} :
      IsCoveredSCtl body → IsCoveredSCtl (.RFor x N body)
  | rIfNz {name : String} {thenBr elseBr : LowCT} :
      IsCoveredSCtl thenBr → IsCoveredSCtl elseBr →
      IsCoveredSCtl (.RIfNz name thenBr elseBr)
  | rLetU64Zero {name : String} {body : LowCT} :
      IsCoveredSCtl body → IsCoveredSCtl (.RLetU64Zero name body)
  | rLetZero {name : String} {tt : TowerType} {body : LowCT} :
      IsCoveredSCtl body → IsCoveredSCtl (.RLetZero name tt body)

/-- `IsCoveredSCtl` refines the control-extended front-simulation coverage
    `IsCoveredCtl` (via `IsCoveredS.toIsCovered` on the straight-line arms), so
    a single `IsCoveredSCtl` hypothesis feeds BOTH the preservation
    homomorphism (`translateDialectControl_denote_ctl`) and the operational
    simulation (`rustExecSimulatesDialect`). -/
theorem IsCoveredSCtl.toIsCoveredCtl {c : LowCT} (h : IsCoveredSCtl c) :
    IsCoveredCtl c := by
  induction h with
  | ofStraight hs => exact .ofCovered hs.toIsCovered
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rFor _ ih => exact .rFor ih
  | rIfNz _ _ ihT ihE => exact .rIfNz ihT ihE
  | rLetU64Zero _ ih => exact .rLetU64Zero ih
  | rLetZero _ ih => exact .rLetZero ih

/-- `asSingleScalarSet` inversion: a successful view IS an `RScalarSet`. -/
theorem asSingleScalarSet_eq : ∀ {c : LowCT} {s : SingleScalarSet},
    asSingleScalarSet c = some s → c = .RScalarSet s.name s.val := by
  intro c s h
  cases c <;>
    first
    | (obtain rfl := Option.some.inj h; rfl)
    | exact absurd h (by simp [asSingleScalarSet])

/-- A left factor appended to a list yielding the list itself is empty. -/
theorem append_eq_self_left {Δ Γ : Ctx} (h : Δ ++ Γ = Γ) : Δ = [] := by
  have hlen := congrArg List.length h
  simp only [List.length_append] at hlen
  exact List.eq_nil_of_length_eq_zero (by omega)

/-! ### 8a. Context-extension invariants of the front chains -/

/-- `lowerSExpr` only pushes slots: its output context is `Δ ++ Γ`. -/
theorem lowerSExpr_ext (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (o : DTransOut Γ) (nm : String)
      (cnt' : Nat),
      TranslateDialectDirectArms.lowerSExpr vm cnt e = some (o, nm, cnt') →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ := by
  induction e with
  | SVar x =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · simp only [Option.some.injEq, Prod.mk.injEq] at hlow
        obtain ⟨rfl, rfl, rfl⟩ := hlow
        exact ⟨[], rfl⟩
      · exact absurd hlow (by simp)
  | SLit n =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr, Option.some.injEq,
        Prod.mk.injEq] at hlow
      obtain ⟨rfl, rfl, rfl⟩ := hlow
      exact ⟨[.sword 64], rfl⟩
  | SLt a b iha ihb =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      exact absurd hlow (by simp)
  | SAsr a b iha ihb =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      exact absurd hlow (by simp)
  | SMulS a b iha ihb =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      exact absurd hlow (by simp)
  | SMulHiS a b iha ihb =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      exact absurd hlow (by simp)
  | SLimb x i =>
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      exact absurd hlow (by simp)
  | _ =>
      -- All eight binary arms share the two-chain `seqOut`/`pushVarBind` shape.
      rename_i a b iha ihb
      intro Γ vm cnt o nm cnt' hlow
      simp only [TranslateDialectDirectArms.lowerSExpr] at hlow
      split at hlow
      · exact absurd hlow (by simp)
      · next r hra =>
          obtain ⟨oa, na, c1⟩ := r
          split at hlow
          · exact absurd hlow (by simp)
          · next s hrb =>
              obtain ⟨ob, nb, c2⟩ := s
              split at hlow
              · next va vb hla hlb =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                  obtain ⟨rfl, rfl, rfl⟩ := hlow
                  obtain ⟨Δa, hΔa⟩ := iha vm cnt oa na c1 hra
                  obtain ⟨Δb, hΔb⟩ := ihb oa.vm c1 ob nb c2 hrb
                  refine ⟨.sword 64 :: (Δb ++ Δa), ?_⟩
                  show .sword 64 :: ob.Γ' = (.sword 64 :: (Δb ++ Δa)) ++ Γ
                  rw [hΔb, hΔa]
                  simp
              · exact absurd hlow (by simp)

/-- `loopCallNDestsD` only pushes slots, one per destination. -/
theorem loopCallNDestsD_ext (fname : String) (args : List Located) :
    ∀ (dests : List Located) {i : Nat} {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      loopCallNDestsD fname args vm dests i = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧ (Δ = [] → dests = []) := by
  intro dests
  induction dests with
  | nil =>
      intro i Γ vm o htr
      simp only [loopCallNDestsD] at htr
      obtain rfl := Option.some.inj htr
      exact ⟨[], rfl, fun _ => rfl⟩
  | cons d rest ih =>
      intro i Γ vm o htr
      rcases hra : resolveLocatedArgs vm args with _ | resolvedArgs
      · simp [loopCallNDestsD, hra] at htr
      · simp only [loopCallNDestsD, hra] at htr
        rcases hrest : loopCallNDestsD fname args (vm.bind d.locVar) rest (i + 1) with _ | oRest
        · rw [hrest] at htr; simp at htr
        · rw [hrest] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          obtain ⟨Δr, hΔr, _⟩ := ih (vm.bind d.locVar) oRest hrest
          refine ⟨Δr ++ [encodeTy d.locDst], ?_, ?_⟩
          · show oRest.Γ' = (Δr ++ [encodeTy d.locDst]) ++ Γ
            rw [hΔr]; simp
          · intro h; exact absurd h (by simp)

/-- **Context-extension + inertness invariant of the straight-line front.**
    Every accepted `translateDialectFull` output context is `Δ ++ Γ` for some
    pushed prefix `Δ` (the front only pushes slots, never pops), and a
    context-invariant translation (`Δ = []`) is env-INERT: `semScalarL ls` is the
    identity on it, for every leaf oracle `ls`. Proved for ALL of `LowCT` (no
    coverage hypothesis) by structural induction — the arms the front declines are
    vacuous. -/
theorem translateDialectFull_extWith (ls : SemLeafSpec) (c : LowCT) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      translateDialectFull vm c = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧
        (Δ = [] → ∀ env env' : SEnvScalar, semScalarL ls c env = some env' → env' = env) := by
  induction c <;> intro Γ vm o htr
  case RSkip =>
      obtain rfl := Option.some.inj htr
      refine ⟨[], rfl, fun _ env env' hsem => ?_⟩
      simp only [semScalarL] at hsem
      exact (Option.some.inj hsem).symm
  case RAssert label =>
      obtain rfl := Option.some.inj htr
      refine ⟨[], rfl, fun _ env env' hsem => ?_⟩
      simp only [semScalarL] at hsem
      exact (Option.some.inj hsem).symm
  case RSeq c₁ c₂ ih₁ ih₂ =>
      rcases ht1 : translateDialectFull vm c₁ with _ | o₁
      · simp [translateDialectFull, ht1] at htr
      · rcases ht2 : translateDialectFull o₁.vm c₂ with _ | o₂
        · simp [translateDialectFull, ht1, ht2] at htr
        · simp only [translateDialectFull, ht1, ht2, Option.some.injEq] at htr
          obtain rfl := htr
          obtain ⟨Δ₁, hΔ₁, hin₁⟩ := ih₁ vm o₁ ht1
          obtain ⟨Δ₂, hΔ₂, hin₂⟩ := ih₂ o₁.vm o₂ ht2
          refine ⟨Δ₂ ++ Δ₁, ?_, ?_⟩
          · show o₂.Γ' = (Δ₂ ++ Δ₁) ++ Γ
            rw [hΔ₂, hΔ₁, List.append_assoc]
          · intro hnil env env' hsem
            obtain ⟨h2, h1⟩ := List.append_eq_nil_iff.mp hnil
            simp only [semScalarL] at hsem
            rcases hs1 : semScalarL ls c₁ env with _ | env₁
            · rw [hs1] at hsem; simp at hsem
            · simp only [hs1, Option.bind_some] at hsem
              rw [hin₂ h2 env₁ env' hsem, hin₁ h1 env env₁ hs1]
  case RBlock body ih =>
      simp only [translateDialectFull] at htr
      obtain ⟨Δ, hΔ, hin⟩ := ih vm o htr
      refine ⟨Δ, hΔ, fun hnil env env' hsem => ?_⟩
      simp only [semScalarL] at hsem
      exact hin hnil env env' hsem
  case RLetZero nm tt body ih =>
      simp only [translateDialectFull] at htr
      obtain ⟨Δ, hΔ, hin⟩ := ih vm o htr
      refine ⟨Δ, hΔ, fun hnil env env' hsem => ?_⟩
      rw [semScalarL_rLetZero] at hsem
      exact hin hnil env env' hsem
  case RLetU64Zero nm body ih =>
      simp only [translateDialectFull] at htr
      rcases htb : translateDialectFull (vm.bind nm) body with _ | ob
      · rw [htb] at htr; simp at htr
      · rw [htb] at htr
        simp only [Option.some.injEq] at htr
        obtain rfl := htr
        obtain ⟨Δb, hΔb, _⟩ := ih (vm.bind nm) ob htb
        refine ⟨Δb ++ [.sword 64], ?_, fun h => absurd h (by simp)⟩
        show ob.Γ' = (Δb ++ [.sword 64]) ++ Γ
        rw [hΔb]; simp
  case RScalarSet nm n =>
      obtain rfl := Option.some.inj htr
      exact ⟨[.sword 64], rfl, fun h => absurd h (by simp)⟩
  case RCall fname dest args =>
      rcases hra : resolveLocatedArgs vm args with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        exact ⟨[encodeTy dest.locDst], rfl, fun h => absurd h (by simp)⟩
  case RSelect dst sel src0 src1 =>
      simp only [translateDialectFull] at htr
      split at htr
      · obtain rfl := Option.some.inj htr
        exact ⟨[.sword 64, .bit, .sword 64], rfl, fun h => absurd h (by simp)⟩
      · rcases hra : resolveLocatedArgs vm [{ locVar := sel, locSrc := .TU64 }, src0, src1]
          with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          exact ⟨[encodeTy dst.locDst], rfl, fun h => absurd h (by simp)⟩
  case RCallDstThreaded fname dst args =>
      rcases hra : resolveLocatedArgs vm (dst :: args) with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        exact ⟨[encodeTy dst.locDst], rfl, fun h => absurd h (by simp)⟩
  case RTupleLoad dst src idx =>
      rcases hra : resolveLocatedArgs vm [src] with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        obtain rfl := Option.some.inj htr
        exact ⟨[encodeTy dst.locDst], rfl, fun h => absurd h (by simp)⟩
  case RArrLoadLit dst src idx =>
      simp only [translateDialectFull] at htr
      split at htr
      · obtain rfl := Option.some.inj htr
        exact ⟨[.sword 64, .sword 64], rfl, fun h => absurd h (by simp)⟩
      · rcases hra : resolveLocatedArgs vm [src] with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          exact ⟨[encodeTy dst.locDst], rfl, fun h => absurd h (by simp)⟩
  case RArrStoreLit arr idx src =>
      simp only [translateDialectFull] at htr
      split at htr
      · rename_i _ n _ _ _ _ _
        obtain rfl := Option.some.inj htr
        exact ⟨[.memref n, .sword 64], rfl, fun h => absurd h (by simp)⟩
      · rcases hra : resolveLocatedArgs vm [arr, src] with _ | resolvedArgs
        · simp [hra] at htr
        · simp only [hra] at htr
          obtain rfl := Option.some.inj htr
          exact ⟨[encodeTy arr.locDst], rfl, fun h => absurd h (by simp)⟩
  case RArrLoad dst src idxVar =>
      rcases hra : resolveLocatedArgs vm [src] with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · rcases hidx : vm.lookup idxVar with _ | idxSig
        · simp [translateDialectFull, hra, hidx] at htr
        · simp only [translateDialectFull, hra, hidx] at htr
          obtain rfl := Option.some.inj htr
          exact ⟨[encodeTy dst.locDst], rfl, fun h => absurd h (by simp)⟩
  case RArrStore arr idxVar src =>
      rcases hra : resolveLocatedArgs vm [arr, src] with _ | resolvedArgs
      · simp [translateDialectFull, hra] at htr
      · rcases hidx : vm.lookup idxVar with _ | idxSig
        · simp [translateDialectFull, hra, hidx] at htr
        · simp only [translateDialectFull, hra, hidx] at htr
          obtain rfl := Option.some.inj htr
          exact ⟨[encodeTy arr.locDst], rfl, fun h => absurd h (by simp)⟩
  case RCallSwap fname dest1 dest2 args =>
      rcases hra : resolveLocatedArgs vm args with _ | ra
      · simp [translateDialectFull, hra] at htr
      · simp only [translateDialectFull, hra] at htr
        rcases hra2 : resolveLocatedArgs (vm.bind dest1.locVar) args with _ | ra2
        · rw [hra2] at htr; simp at htr
        · rw [hra2] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          exact ⟨[encodeTy dest2.locDst, encodeTy dest1.locDst], rfl,
            fun h => absurd h (by simp)⟩
  case RCloneCall cv tt oldDest innerF newDest args =>
      rcases hlk : vm.lookup oldDest.locVar with _ | p
      · simp [translateDialectFull, hlk] at htr
      · obtain ⟨cloneTy, oldVar⟩ := p
        simp only [translateDialectFull, hlk] at htr
        rcases hra : resolveLocatedArgs (vm.bind cv) args with _ | ra
        · rw [hra] at htr; simp at htr
        · rw [hra] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          exact ⟨[encodeTy newDest.locDst, cloneTy], rfl, fun h => absurd h (by simp)⟩
  case RLimbStore loc idx v =>
      rcases hlk : vm.lookup loc.locVar with _ | p
      · simp only [translateDialectFull, hlk] at htr
        rcases hen : encodeTy loc.locDst with _ | _ | _ | _ | _ | n
        all_goals (rw [hen] at htr; dsimp only at htr)
        case memrefW => exact absurd htr (by simp)
        iterate 5 (exact absurd htr (by simp))
        by_cases hlt : idx < n
        · rw [if_pos hlt] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          exact ⟨[.memref n, .sword 64], rfl, fun h => absurd h (by simp)⟩
        · rw [if_neg hlt] at htr; simp at htr
      · obtain ⟨mt, arr⟩ := p
        rcases mt with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | n
        case memrefW => simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp [translateDialectFull, hlk] at htr
        · simp only [translateDialectFull, hlk] at htr
          by_cases hlt : idx < n
          · rw [dif_pos hlt] at htr
            simp only [Option.some.injEq] at htr
            obtain rfl := htr
            exact ⟨[.memref n, .sword 64], rfl, fun h => absurd h (by simp)⟩
          · rw [dif_neg hlt] at htr; simp at htr
  case RCallN fname dests args =>
      simp only [translateDialectFull] at htr
      obtain ⟨Δ, hΔ, hnil⟩ := loopCallNDestsD_ext fname args dests vm o htr
      refine ⟨Δ, hΔ, fun h env env' hsem => ?_⟩
      obtain rfl := hnil h
      simp only [semScalarL, semCallNDestsL] at hsem
      exact (Option.some.inj hsem).symm
  case RScalarSetExpr x e =>
      rcases hlow : TranslateDialectDirectArms.lowerSExpr vm 0 e with _ | r
      · simp [translateDialectFull, hlow] at htr
      · obtain ⟨oe, nme, cnte⟩ := r
        rcases hlk : TranslateDialectDirectArms.lookupU64 oe.vm nme with _ | v
        · simp [translateDialectFull, hlow, hlk] at htr
        · simp only [translateDialectFull, hlow, hlk] at htr
          obtain rfl := Option.some.inj htr
          obtain ⟨Δe, hΔe⟩ := lowerSExpr_ext e vm 0 oe nme cnte hlow
          refine ⟨.sword 64 :: Δe, ?_, fun h => absurd h (by simp)⟩
          show .sword 64 :: oe.Γ' = (.sword 64 :: Δe) ++ Γ
          rw [hΔe]; rfl
  all_goals simp [translateDialectFull] at htr

/-- **Context-extension + inertness invariant of the straight-line front**
    (`translateDialectFull_extWith` at `defaultLeaf`). -/
theorem translateDialectFull_ext (c : LowCT) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      translateDialectFull vm c = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧
        (Δ = [] → ∀ env env' : SEnvScalar, semScalar c env = some env' → env' = env) := by
  rw [semScalar_eq_semScalarL]
  exact translateDialectFull_extWith defaultLeaf c

/-- `loopRForD` only pushes slots (one counter bind + the body's pushes per
    trip); a context-invariant unroll is the zero-trip one. -/
theorem loopRForD_ext (x : String) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      translateDialectControl vm body = some o → ∃ Δ : Ctx, o.Γ' = Δ ++ Γ) :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
        vm x N = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧ (Δ = [] → N = 0) := by
  intro N
  induction N with
  | zero =>
      intro Γ vm o htr
      simp only [loopRForD] at htr
      obtain rfl := Option.some.inj htr
      exact ⟨[], rfl, fun _ => rfl⟩
  | succ n ihN =>
      intro Γ vm o htr
      simp only [loopRForD] at htr
      rcases hpre : loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
          vm x n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hbt : translateDialectControl (oPre.vm.bind x) body with _ | oBody
        · rw [hbt] at htr; simp at htr
        · simp only [hbt, Option.some.injEq] at htr
          obtain rfl := htr
          obtain ⟨ΔP, hΔP, _⟩ := ihN vm oPre hpre
          obtain ⟨Δb, hΔb⟩ := ihBody (oPre.vm.bind x) oBody hbt
          refine ⟨Δb ++ .sword 64 :: ΔP, ?_, fun h => absurd h (by simp)⟩
          show oBody.Γ' = (Δb ++ .sword 64 :: ΔP) ++ Γ
          rw [hΔb, hΔP]
          simp

/-- **Context-extension + inertness invariant of the control front.** The
    control-arm analogue of `translateDialectFull_ext`: every accepted
    `translateDialectControl` output context is `Δ ++ Γ`, and `Δ = []` forces
    env-inertness of `semScalarL ls` for every leaf oracle `ls`. Proved for ALL of
    `LowCT`; the non-control arms delegate to the straight-line invariant. -/
theorem translateDialectControl_extWith (ls : SemLeafSpec) (c : LowCT) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      translateDialectControl vm c = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧
        (Δ = [] → ∀ env env' : SEnvScalar, semScalarL ls c env = some env' → env' = env) := by
  induction c <;> intro Γ vm o htr
  case RSeq c₁ c₂ ih1 ih2 =>
      -- Control-level `RSeq`: the front recurses into `translateDialectControl`
      -- on both children; the pushed context is `Δ₂ ++ Δ₁` and inertness chains
      -- through `semScalar (RSeq _ _) = bind`.
      simp only [translateDialectControl] at htr
      split at htr
      · rename_i o₁ h1
        split at htr
        · rename_i o₂ h2
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          obtain ⟨Δ₁, hΔ₁, hin₁⟩ := ih1 vm o₁ h1
          obtain ⟨Δ₂, hΔ₂, hin₂⟩ := ih2 o₁.vm o₂ h2
          refine ⟨Δ₂ ++ Δ₁, ?_, ?_⟩
          · show o₂.Γ' = (Δ₂ ++ Δ₁) ++ Γ
            rw [hΔ₂, hΔ₁, List.append_assoc]
          · intro hnil env env' hsem
            obtain ⟨h2nil, h1nil⟩ := List.append_eq_nil_iff.mp hnil
            simp only [semScalarL] at hsem
            rcases hs1 : semScalarL ls c₁ env with _ | env₁
            · rw [hs1] at hsem; simp at hsem
            · simp only [hs1, Option.bind_some] at hsem
              rw [hin₂ h2nil env₁ env' hsem]
              exact hin₁ h1nil env env₁ hs1
        · exact absurd htr (by simp)
      · exact absurd htr (by simp)
  case RFor x N body ih =>
      simp only [translateDialectControl] at htr
      obtain ⟨Δ, hΔ, hN⟩ := loopRForD_ext x body
        (fun {Γ} vm o h => ((ih vm o h).imp fun Δ p => p.1)) N vm o htr
      refine ⟨Δ, hΔ, ?_⟩
      intro hnil env env' hsem
      obtain rfl := hN hnil
      simp only [semScalarL, semRForD] at hsem
      exact (Option.some.inj hsem).symm
  case RWhileNz name body ih =>
      simp only [translateDialectControl] at htr
      split at htr
      · rcases hb : translateDialectControl vm body with _ | ob
        · rw [hb] at htr; simp at htr
        · rw [hb] at htr
          simp only [Option.map_some, Option.some.injEq] at htr
          obtain rfl := htr
          refine ⟨[], rfl, fun _ env env' hsem => ?_⟩
          simp only [semScalarL] at hsem
          exact absurd hsem (by simp)
      · exact absurd htr (by simp)
  case RIfNz name thenBr elseBr ihT ihE =>
      simp only [translateDialectControl] at htr
      split at htr
      case _ w condVar hlk =>
        split at htr
        case _ o₁ o₂ ht₁ ht₂ =>
          split at htr
          · next h₁ =>
            split at htr
            · next h₂ =>
              -- (A): both branches context-invariant; the front passes `o₁`
              -- through, and BOTH branches are env-inert.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              refine ⟨[], h₁, fun _ env env' hsem => ?_⟩
              simp only [semScalarL] at hsem
              split at hsem
              case _ w' condv henv =>
                rcases hts : asSingleScalarSet thenBr with _ | tS
                · simp only [hts] at hsem
                  rcases hs1 : semScalarL ls thenBr env with _ | env₁
                  · rw [hs1] at hsem; simp at hsem
                  · simp only [hs1, Option.bind_some] at hsem
                    obtain ⟨Δ₁, hΔ₁, hin₁⟩ := ihT vm o₁ ht₁
                    obtain ⟨Δ₂, hΔ₂, hin₂⟩ := ihE vm o₂ ht₂
                    rw [hin₂ (append_eq_self_left (hΔ₂ ▸ h₂)) env₁ env' hsem,
                      hin₁ (append_eq_self_left (hΔ₁ ▸ h₁)) env env₁ hs1]
                · -- `thenBr` a single `RScalarSet` always extends — contra `h₁`.
                  obtain rfl := asSingleScalarSet_eq hts
                  have h1' : (CryptoTy.sword 64 :: Γ : Ctx) = o₁.Γ' :=
                    congrArg DTransOut.Γ' (Option.some.inj ht₁)
                  rw [← h1'] at h₁
                  exact absurd (congrArg List.length h₁) (by simp)
              case _ => exact absurd hsem (by simp)
            · next h₂ =>
              -- (B1): only `elseBr` extends; the front passes `o₂` through.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              obtain ⟨Δ₂, hΔ₂, _⟩ := ihE vm o₂ ht₂
              exact ⟨Δ₂, hΔ₂,
                fun hnil => absurd (show o₂.Γ' = Γ by rw [hΔ₂, hnil]; rfl) h₂⟩
          · next h₁ =>
            split at htr
            · next h₂ =>
              -- (B2): only `thenBr` extends; the front passes `o₁` through.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              obtain ⟨Δ₁, hΔ₁, _⟩ := ihT vm o₁ ht₁
              exact ⟨Δ₁, hΔ₁,
                fun hnil => absurd (show o₁.Γ' = Γ by rw [hΔ₁, hnil]; rfl) h₁⟩
            · next h₂ =>
              split at htr
              · next tS eS hts hes =>
                split at htr
                · next hname =>
                  -- (C′) φ-merge: six pushed slots.
                  simp only [Option.some.injEq] at htr
                  obtain rfl := htr
                  exact ⟨[.sword 64, .bit, .bit, .sword w, .sword 64, .sword 64],
                    rfl, fun h => absurd h (by simp)⟩
                · next hname =>
                  -- (C-otherwise, names differ): sequential re-translation.
                  split at htr
                  · next o₂' ht₂' =>
                    simp only [Option.some.injEq] at htr
                    obtain rfl := htr
                    obtain ⟨Δ₁, hΔ₁, _⟩ := ihT vm o₁ ht₁
                    obtain ⟨Δ₂', hΔ₂', _⟩ := ihE o₁.vm o₂' ht₂'
                    refine ⟨Δ₂' ++ Δ₁, ?_, ?_⟩
                    · show o₂'.Γ' = (Δ₂' ++ Δ₁) ++ Γ
                      rw [hΔ₂', hΔ₁, List.append_assoc]
                    · intro hnil
                      obtain ⟨h2, h1⟩ := List.append_eq_nil_iff.mp hnil
                      exact absurd (show o₁.Γ' = Γ by rw [hΔ₁, h1]; rfl) h₁
                  · exact absurd htr (by simp)
              · -- (C-otherwise, not both single scalar-sets): same shape.
                split at htr
                · next o₂' ht₂' =>
                  simp only [Option.some.injEq] at htr
                  obtain rfl := htr
                  obtain ⟨Δ₁, hΔ₁, _⟩ := ihT vm o₁ ht₁
                  obtain ⟨Δ₂', hΔ₂', _⟩ := ihE o₁.vm o₂' ht₂'
                  refine ⟨Δ₂' ++ Δ₁, ?_, ?_⟩
                  · show o₂'.Γ' = (Δ₂' ++ Δ₁) ++ Γ
                    rw [hΔ₂', hΔ₁, List.append_assoc]
                  · intro hnil
                    obtain ⟨h2, h1⟩ := List.append_eq_nil_iff.mp hnil
                    exact absurd (show o₁.Γ' = Γ by rw [hΔ₁, h1]; rfl) h₁
                · exact absurd htr (by simp)
        case _ => exact absurd htr (by simp)
      case _ => exact absurd htr (by simp)
  case RLetZero nm tt body ih =>
      rw [translateDialectControl_rLetZero] at htr
      obtain ⟨Δ, hΔ, hin⟩ := ih vm o htr
      refine ⟨Δ, hΔ, fun hnil env env' hsem => ?_⟩
      rw [semScalarL_rLetZero] at hsem
      exact hin hnil env env' hsem
  case RLetU64Zero nm body ih =>
      rw [translateDialectControl_rLetU64Zero] at htr
      rcases htb : translateDialectControl (vm.bind nm) body with _ | ob
      · rw [htb] at htr; simp at htr
      · rw [htb] at htr
        simp only [Option.some.injEq] at htr
        obtain rfl := htr
        obtain ⟨Δb, hΔb, _⟩ := ih (vm.bind nm) ob htb
        refine ⟨Δb ++ [.sword 64], ?_, fun h => absurd h (by simp)⟩
        show ob.Γ' = (Δb ++ [.sword 64]) ++ Γ
        rw [hΔb]; simp
  all_goals exact translateDialectFull_extWith ls _ vm o htr

/-- **Context-extension + inertness invariant of the control front**
    (`translateDialectControl_extWith` at `defaultLeaf`). -/
theorem translateDialectControl_ext (c : LowCT) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (o : DTransOut Γ),
      translateDialectControl vm c = some o →
      ∃ Δ : Ctx, o.Γ' = Δ ++ Γ ∧
        (Δ = [] → ∀ env env' : SEnvScalar, semScalar c env = some env' → env' = env) := by
  rw [semScalar_eq_semScalarL]
  exact translateDialectControl_extWith defaultLeaf c

/-- Context-invariant accepted translations are env-inert under `semScalarL ls`
    (corollary of `translateDialectControl_extWith`). The `RIfNz` (A)/(B)
    pass-through cases of the preservation theorem reduce their discarded branch
    to this. -/
theorem translateDialectControl_inertWith (ls : SemLeafSpec) {c : LowCT} {Γ : Ctx}
    {vm : VarMap Γ} {o : DTransOut Γ} (htr : translateDialectControl vm c = some o)
    (hΓ : o.Γ' = Γ) :
    ∀ env env' : SEnvScalar, semScalarL ls c env = some env' → env' = env := by
  obtain ⟨Δ, hΔ, hin⟩ := translateDialectControl_extWith ls c vm o htr
  exact hin (append_eq_self_left (hΔ ▸ hΓ))

/-- Context-invariant accepted translations are env-inert (corollary of
    `translateDialectControl_ext`). -/
theorem translateDialectControl_inert {c : LowCT} {Γ : Ctx} {vm : VarMap Γ}
    {o : DTransOut Γ} (htr : translateDialectControl vm c = some o)
    (hΓ : o.Γ' = Γ) :
    ∀ env env' : SEnvScalar, semScalar c env = some env' → env' = env := by
  rw [semScalar_eq_semScalarL]
  exact translateDialectControl_inertWith defaultLeaf htr hΓ

/-! ### 8b. The `RFor` induction case (`loopRForD_denote`)

`Nat`-induction over the meta-unroll, in lock-step with `semRForD`: the
`n+1`-trip prefix is (trips `0..n-1`) ∘ (counter bind `x := n`) ∘ (body), each
composed via `ComCont.comp` — the `loopCallNDestsD_denote` fold pattern with
the body IH in place of the opaque `extCall` bind. The entry `Γ`/`vm`/`V`/`env`
stay FIXED across the induction (the recursion peels the LAST trip, re-entering
at the same entry state); only the output `o`/`env'` generalize. -/

/-- Front-general preservation over the `RFor` meta-unroll at the leaf oracle `ls`.
    The body's preservation homomorphism is passed in (`ihBody`, the coverage IH). -/
theorem loopRForD_denoteWith (ls : SemLeafSpec) (x : String) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm body = some o →
      semScalarL ls body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V') :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
        vm x N = some o →
      semRForD (fun e => semScalarL ls body e) x N env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  intro N
  induction N with
  | zero =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopRForD] at htr
      simp only [semRForD] at hsem
      obtain rfl := Option.some.inj htr
      obtain rfl := Option.some.inj hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | succ n ihN =>
      intro Γ vm V env env' o hc htr hsem
      simp only [loopRForD] at htr
      simp only [semRForD] at hsem
      rcases hpre : loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
          vm x n with _ | oPre
      · rw [hpre] at htr; simp at htr
      · simp only [hpre] at htr
        rcases hspre : semRForD (fun e => semScalarL ls body e) x n env with _ | envPre
        · rw [hspre] at hsem; simp at hsem
        · simp only [hspre] at hsem
          rcases hbt : translateDialectControl (oPre.vm.bind x) body with _ | oBody
          · rw [hbt] at htr; simp at htr
          · simp only [hbt, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨VPre, hcPre, hcontPre⟩ := ihN vm V env envPre oPre hc hpre hspre
            obtain ⟨hconsSet, hcontSet⟩ :=
              scalar_stepWith ls oPre.vm VPre envPre hcPre x
                ({ op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil } :
                  Expr catCryptDialect oPre.Γ' (.sword 64))
            obtain ⟨Vb, hcB, hcontB⟩ :=
              ihBody (oPre.vm.bind x) (VPre.extend _) _ env' oBody hconsSet hbt hsem
            refine ⟨Vb, hcB, ?_⟩
            intro t tail
            obtain ⟨comB, hcomB, hdenB⟩ := hcontB tail
            obtain ⟨comS, hcomS, hdenS⟩ := hcontSet comB
            obtain ⟨com, hcom, hden⟩ := hcontPre comS
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp oPre.cont
                (ComCont.comp (ComCont.varBind _) oBody.cont) tail = some com
              simp only [ComCont.comp, hcomB, hcomS, hcom]
            · exact hden.trans (hdenS.trans hdenB)

/-- Front-general preservation over the `RFor` meta-unroll
    (`loopRForD_denoteWith` at `defaultLeaf`). -/
theorem loopRForD_denote (x : String) (body : LowCT)
    (ihBody : ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm body = some o →
      semScalar body env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V') :
    ∀ (N : Nat) {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      loopRForD (translateBody := fun vm' => translateDialectControl vm' body)
        vm x N = some o →
      semRForD (fun e => semScalar body e) x N env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  rw [semScalar_eq_semScalarL, ← catCryptDenoteWith_default] at ihBody
  rw [semScalar_eq_semScalarL, ← catCryptDenoteWith_default]
  exact loopRForD_denoteWith defaultLeaf x body ihBody

/-! ### 8c. The `RIfNz` (C′) φ-merge expression -/

/-- The φ-merge `ite` expression the front's (C′) case emits, at its context
    `Γ₅ = .bit :: .bit :: .sword w :: .sword 64 :: .sword 64 :: Γ` (cond-bit,
    cond-eq, zero, elseV, thenV, entry). Definitionally the front's `eIte`. -/
def phiIteExpr {Γ : Ctx} (w : Nat) :
    Expr catCryptDialect
      (.bit :: .bit :: .sword w :: .sword 64 :: .sword 64 :: Γ) (.sword 64) :=
  { op := .ite (.sword 64), retTy_eq := rfl,
    args := .cons (toVIRVar .here)
      (.cons (toVIRVar (.there (.there (.there (.there .here)))))
        (.cons (toVIRVar (.there (.there (.there .here)))) .nil)) }

/-- The φ-merge chain denotes the cmov select: at the valuation the five
    preceding merge binds build, the front's `ite` computes exactly
    `phiSelect condval thenV elseV` (`zero → else`, `nonzero → then`). -/
theorem phiIteExpr_denote {Γ : Ctx} (w : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (condval : BitVec w)
    (tv ev : BitVec 64) :
    (phiIteExpr (Γ := Γ) w).denote
      (.cons (!decide (condval = 0#w))
        (.cons (decide (condval = 0#w))
          (.cons (BitVec.ofNat w 0) (.cons ev (.cons tv V)))))
      = phiSelect condval tv ev := by
  show (if (!decide (condval = 0#w)) = true then tv else ev) = phiSelect condval tv ev
  by_cases hcv : condval = 0#w <;> simp [phiSelect, hcv]

/-! ### 8d. Front-general scalar preservation over the FULL control-extended
fragment -/

/-- **Front-general scalar preservation at a leaf oracle, control-extended.**
    For every leaf oracle `ls` and any `IsCoveredSCtl`-covered body — the full
    `IsCoveredCtl`-shaped fragment, `RFor` and `RIfNz` included — the emitted
    `Com`-prefix, denoted under `catCryptDenoteWith ls`, denotes exactly the body's
    `semScalarL ls` waist semantics.
    Induction on the coverage: the straight-line arms delegate to
    `translateDialectFull_denoteWith`; `RFor` is `loopRForD_denoteWith`'s meta-unroll
    induction; `RIfNz` follows the front's four-way case split — the (A)/(B)
    pass-through cases discharge the discarded (context-invariant) branch via
    `translateDialectControl_inertWith`, the (C′) φ-merge composes five
    `consistentS_weaken` steps with one `scalar_stepWith` on `phiIteExpr` (its
    value reconciled by `phiIteExpr_denote`), and (C-otherwise) is the `RSeq`
    spine over the re-translated `elseBr`. -/
theorem translateDialectControl_denote_ctlWith (ls : SemLeafSpec) {c : LowCT}
    (hcov : IsCoveredSCtl c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm c = some o →
      semScalarL ls c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧
            @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ com V
              = @Com.denote catCryptDialect _ _ (catCryptDenoteWith ls) _ _ tail V' := by
  induction hcov with
  | @ofStraight c hs =>
      intro Γ vm V env env' o hc htr hsem
      have hfull : translateDialectControl vm c = translateDialectFull vm c :=
        translateDialectControl_eq_full_of_covered vm hs.toIsCovered
      rw [hfull] at htr
      exact translateDialectFull_denoteWith ls hs vm V env env' o hc htr hsem
  | @rFor x N body hbody ih =>
      intro Γ vm V env env' o hc htr hsem
      exact loopRForD_denoteWith ls x body
        (fun vm V env env' o hc ht hs => ih vm V env env' o hc ht hs)
        N vm V env env' o hc htr hsem
  | @rSeq c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      -- The control-level sequence: the two child prefixes composed, the waist
      -- the `bind` of the two child waists.
      intro Γ vm V env env' o hc htr hsem
      rw [translateDialectControl_rSeq] at htr
      rcases ht₁ : translateDialectControl vm c₁ with _ | o₁
      · rw [ht₁] at htr; simp at htr
      · simp only [ht₁] at htr
        rcases ht₂ : translateDialectControl o₁.vm c₂ with _ | o₂
        · rw [ht₂] at htr; simp at htr
        · rw [ht₂] at htr
          simp only [Option.some.injEq] at htr
          obtain rfl := htr
          simp only [semScalarL] at hsem
          rcases hs1 : semScalarL ls c₁ env with _ | env₁
          · rw [hs1] at hsem; simp at hsem
          · simp only [hs1, Option.bind_some] at hsem
            obtain ⟨V₁, hc₁, hcont₁⟩ := ih₁ vm V env env₁ o₁ hc ht₁ hs1
            obtain ⟨V₂, hc₂, hcont₂⟩ := ih₂ o₁.vm V₁ env₁ env' o₂ hc₁ ht₂ hsem
            refine ⟨V₂, hc₂, ?_⟩
            intro t tail
            obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
            obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp o₁.cont o₂.cont tail = some com
              simp only [ComCont.comp, hcom₂, hcom]
            · rw [hden, hden₂]
  | @rLetZero name tt body hbody ih =>
      -- The front emits nothing for the binder and the waist is the body's.
      intro Γ vm V env env' o hc htr hsem
      rw [translateDialectControl_rLetZero] at htr
      rw [semScalarL_rLetZero] at hsem
      exact ih vm V env env' o hc htr hsem
  | @rLetU64Zero name body hbody ih =>
      -- The `bvConst 64 0` binding of `name` is one `scalar_stepWith`, composed
      -- with the body IH at the extended context.
      intro Γ vm V env env' o hc htr hsem
      rw [translateDialectControl_rLetU64Zero] at htr
      rcases htb : translateDialectControl (vm.bind name) body with _ | ob
      · rw [htb] at htr; simp at htr
      · rw [htb] at htr
        simp only [Option.some.injEq] at htr
        obtain rfl := htr
        obtain ⟨hcons0, hcont0⟩ :=
          scalar_stepWith ls vm V env hc name
            ({ op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil } :
              Expr catCryptDialect Γ (.sword 64))
        simp only [semScalarL] at hsem
        obtain ⟨V', hc', hcont1⟩ :=
          ih (vm.bind name) (V.extend _) _ env' ob hcons0 htb hsem
        refine ⟨V', hc', ?_⟩
        intro t tail
        obtain ⟨com1, hcom1, hden1⟩ := hcont1 tail
        obtain ⟨com, hcom, hden⟩ := hcont0 com1
        refine ⟨com, ?_, ?_⟩
        · show ComCont.comp (ComCont.varBind _) ob.cont tail = some com
          simp only [ComCont.comp, hcom1, hcom]
        · rw [hden, hden1]
  | @rIfNz name thenBr elseBr hthen helse ihT ihE =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectControl] at htr
      split at htr
      case _ w condVar hlk =>
        have henv : env name = some ⟨CryptoTy.sword w, (toVIRVar condVar).lookup V⟩ := by
          rw [← hc name, hlk]; rfl
        simp only [semScalarL, henv] at hsem
        split at htr
        case _ o₁ o₂ ht₁ ht₂ =>
          split at htr
          · next h₁ =>
            split at htr
            · next h₂ =>
              -- (A): both branches context-invariant; front = `o₁`, and both
              -- branches are env-inert.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              have hseq : (semScalarL ls thenBr env).bind
                  (fun e => semScalarL ls elseBr e) = some env' := by
                rcases hts : asSingleScalarSet thenBr with _ | tS
                · simpa only [hts] using hsem
                · obtain rfl := asSingleScalarSet_eq hts
                  have h1' : (CryptoTy.sword 64 :: Γ : Ctx) = o₁.Γ' :=
                    congrArg DTransOut.Γ' (Option.some.inj ht₁)
                  rw [← h1'] at h₁
                  exact absurd (congrArg List.length h₁) (by simp)
              rcases hs1 : semScalarL ls thenBr env with _ | env₁
              · rw [hs1] at hseq; simp at hseq
              · simp only [hs1, Option.bind_some] at hseq
                rw [translateDialectControl_inertWith ls ht₂ h₂ env₁ env' hseq]
                exact ihT vm V env env₁ o₁ hc ht₁ hs1
            · next h₂ =>
              -- (B1): only `elseBr` extends; `thenBr` is inert, front = `o₂`.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              have hseq : (semScalarL ls thenBr env).bind
                  (fun e => semScalarL ls elseBr e) = some env' := by
                rcases hts : asSingleScalarSet thenBr with _ | tS
                · simpa only [hts] using hsem
                · obtain rfl := asSingleScalarSet_eq hts
                  have h1' : (CryptoTy.sword 64 :: Γ : Ctx) = o₁.Γ' :=
                    congrArg DTransOut.Γ' (Option.some.inj ht₁)
                  rw [← h1'] at h₁
                  exact absurd (congrArg List.length h₁) (by simp)
              rcases hs1 : semScalarL ls thenBr env with _ | env₁
              · rw [hs1] at hseq; simp at hseq
              · simp only [hs1, Option.bind_some] at hseq
                rw [translateDialectControl_inertWith ls ht₁ h₁ env env₁ hs1] at hseq
                exact ihE vm V env env' o₂ hc ht₂ hseq
          · next h₁ =>
            split at htr
            · next h₂ =>
              -- (B2): only `thenBr` extends; `elseBr` is inert, front = `o₁`.
              simp only [Option.some.injEq] at htr
              obtain rfl := htr
              have hseq : (semScalarL ls thenBr env).bind
                  (fun e => semScalarL ls elseBr e) = some env' := by
                rcases hts : asSingleScalarSet thenBr with _ | tS
                · simpa only [hts] using hsem
                · rcases hes : asSingleScalarSet elseBr with _ | eS
                  · simpa only [hts, hes] using hsem
                  · obtain rfl := asSingleScalarSet_eq hes
                    have h2' : (CryptoTy.sword 64 :: Γ : Ctx) = o₂.Γ' :=
                      congrArg DTransOut.Γ' (Option.some.inj ht₂)
                    rw [← h2'] at h₂
                    exact absurd (congrArg List.length h₂) (by simp)
              rcases hs1 : semScalarL ls thenBr env with _ | env₁
              · rw [hs1] at hseq; simp at hseq
              · simp only [hs1, Option.bind_some] at hseq
                obtain ⟨V₁, hc₁, hcont₁⟩ := ihT vm V env env₁ o₁ hc ht₁ hs1
                obtain rfl := translateDialectControl_inertWith ls ht₂ h₂ env₁ env' hseq
                exact ⟨V₁, hc₁, hcont₁⟩
            · next h₂ =>
              split at htr
              · next tS eS hts hes =>
                split at htr
                · next hname =>
                  -- (C′) φ-merge: five weaken steps + one `scalar_step` on the
                  -- merge `ite`, value reconciled by `phiIteExpr_denote`.
                  simp only [Option.some.injEq] at htr
                  obtain rfl := htr
                  simp only [hts, hes] at hsem
                  rw [if_pos hname] at hsem
                  obtain rfl := Option.some.inj hsem
                  have hc1 := consistentS_weaken vm V env hc
                    (t := CryptoTy.sword 64) (BitVec.ofNat 64 tS.val)
                  have hc2 := consistentS_weaken _ _ env hc1
                    (t := CryptoTy.sword 64) (BitVec.ofNat 64 eS.val)
                  have hc3 := consistentS_weaken _ _ env hc2
                    (t := CryptoTy.sword w) (BitVec.ofNat w 0)
                  have hc4 := consistentS_weaken _ _ env hc3
                    (t := CryptoTy.bit) (condIsZero ((toVIRVar condVar).lookup V))
                  have hc5 := consistentS_weaken _ _ env hc4
                    (t := CryptoTy.bit) (!condIsZero ((toVIRVar condVar).lookup V))
                  obtain ⟨hcons, _⟩ :=
                    scalar_stepWith ls _ _ env hc5 tS.name (phiIteExpr (Γ := Γ) w)
                  rw [← phiIteExpr_denote w V ((toVIRVar condVar).lookup V)
                    (BitVec.ofNat 64 tS.val) (BitVec.ofNat 64 eS.val)]
                  exact ⟨_, hcons, fun tail => ⟨_, rfl, rfl⟩⟩
                · next hname =>
                  -- (C-otherwise, names differ): sequential re-translation —
                  -- the `RSeq` spine.
                  split at htr
                  · next o₂' ht₂' =>
                    simp only [Option.some.injEq] at htr
                    obtain rfl := htr
                    simp only [hts, hes] at hsem
                    rw [if_neg hname] at hsem
                    rcases hs1 : semScalarL ls thenBr env with _ | env₁
                    · rw [hs1] at hsem; simp at hsem
                    · simp only [hs1, Option.bind_some] at hsem
                      obtain ⟨V₁, hc₁, hcont₁⟩ := ihT vm V env env₁ o₁ hc ht₁ hs1
                      obtain ⟨V₂, hc₂, hcont₂⟩ :=
                        ihE o₁.vm V₁ env₁ env' o₂' hc₁ ht₂' hsem
                      refine ⟨V₂, hc₂, ?_⟩
                      intro t tail
                      obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
                      obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
                      refine ⟨com, ?_, ?_⟩
                      · show ComCont.comp o₁.cont o₂'.cont tail = some com
                        simp only [ComCont.comp, hcom₂, hcom]
                      · rw [hden, hden₂]
                  · exact absurd htr (by simp)
              · -- (C-otherwise, not both single scalar-sets): same spine.
                rename_i hnot
                split at htr
                · next o₂' ht₂' =>
                  simp only [Option.some.injEq] at htr
                  obtain rfl := htr
                  have hseq : (semScalarL ls thenBr env).bind
                      (fun e => semScalarL ls elseBr e) = some env' := by
                    rcases hts : asSingleScalarSet thenBr with _ | tS
                    · simpa only [hts] using hsem
                    · rcases hes : asSingleScalarSet elseBr with _ | eS
                      · simpa only [hts, hes] using hsem
                      · exact (hnot tS eS hts hes).elim
                  rcases hs1 : semScalarL ls thenBr env with _ | env₁
                  · rw [hs1] at hseq; simp at hseq
                  · simp only [hs1, Option.bind_some] at hseq
                    obtain ⟨V₁, hc₁, hcont₁⟩ := ihT vm V env env₁ o₁ hc ht₁ hs1
                    obtain ⟨V₂, hc₂, hcont₂⟩ :=
                      ihE o₁.vm V₁ env₁ env' o₂' hc₁ ht₂' hseq
                    refine ⟨V₂, hc₂, ?_⟩
                    intro t tail
                    obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
                    obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
                    refine ⟨com, ?_, ?_⟩
                    · show ComCont.comp o₁.cont o₂'.cont tail = some com
                      simp only [ComCont.comp, hcom₂, hcom]
                    · rw [hden, hden₂]
                · exact absurd htr (by simp)
        case _ => exact absurd htr (by simp)
      case _ => exact absurd htr (by simp)

/-- **Front-general scalar preservation, control-extended** (Stage 2).
    For any `IsCoveredSCtl`-covered body — the full
    `IsCoveredCtl`-shaped fragment, `RFor` and `RIfNz` included — the emitted
    `Com`-prefix denotes exactly the body's `semScalar` waist semantics. The
    instance of `translateDialectControl_denote_ctlWith` at `defaultLeaf`. -/
theorem translateDialectControl_denote_ctl {c : LowCT} (hcov : IsCoveredSCtl c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm c = some o →
      semScalar c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [semScalar_eq_semScalarL] at hsem
  have h := translateDialectControl_denote_ctlWith defaultLeaf hcov vm V env env' o hc htr hsem
  rwa [catCryptDenoteWith_default] at h

/-! ### 8e. Worked examples (the `IsCoveredCtl`-shaped fragment) -/

/-- A bounded loop over a covered straight-line body is Stage-2 covered
    (mirrors `TranslateDialectDirectControl`'s `IsCoveredCtl` example). -/
example (x : String) (N : Nat) : IsCoveredSCtl (.RFor x N .RSkip) :=
  .rFor (.ofStraight .rSkip)

/-- An `RIfNz` over covered branches is Stage-2 covered — here the (C′)
    φ-merge shape (both branches single same-name scalar sets). -/
example (name y : String) :
    IsCoveredSCtl (.RIfNz name (.RScalarSet y 1) (.RScalarSet y 0)) :=
  .rIfNz (.ofStraight (.rScalarSet y 1)) (.ofStraight (.rScalarSet y 0))

/-- Nested control: a conditional inside a bounded loop is Stage-2 covered. -/
example (x name y : String) (N : Nat) :
    IsCoveredSCtl (.RFor x N (.RIfNz name (.RScalarSet y 1) (.RScalarSet y 0))) :=
  .rFor (.rIfNz (.ofStraight (.rScalarSet y 1)) (.ofStraight (.rScalarSet y 0)))

/-- A loop body carrying a contract assertion is Stage-2 covered: `IsCoveredSCtl`
    picks the assertion up through `ofStraight`. -/
example (x label y : String) (N : Nat) :
    IsCoveredSCtl (.RFor x N (.RSeq (.RAssert label) (.RScalarSet y 1))) :=
  .rFor (.ofStraight (.rSeq (.rAssert label) (.rScalarSet y 1)))

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
