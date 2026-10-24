/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.MlkemFieldLeaf
public import CatCrypt.Crypto.SecureCompilation.Ascent.StoreRefinement
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres

/-!
# The value abstraction of the ascent calculus

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

A `ValueAbs C A` is the value-level half of an ascent state relation: an encoding
`enc : C → A` of a concrete carrier into an abstract one, together with the
refinement predicate `Refines : C → A → Prop` a state relation reads pointwise.
`Refines` defaults to the graph of `enc`; an abstraction with a side condition on
the concrete representative (the canonical range of an ML-KEM coefficient)
restricts it. The one law, `enc_of_refines`, says `Refines` is a subgraph of the
encoding, so every abstraction is functional.

The store relations are then generic in the abstraction: `SRof V` over the
scalar environment `SEnvScalar` (non-temp names, the shape of `SRwordNT`) and
`SRcarryOf V` over the register file of a `JState 64` with the carry flag. The
bespoke relations of the earlier leaves are instances:

| bespoke relation | abstraction |
|---|---|
| `SRwordNT` (`ExprLeaf`) | `SRof wordAbs` |
| `SRwordBV` (`ExprLeaf`) | `SRof bvAbs` |
| `SRfqVal` / `SRfqCanon` (`MlkemFieldLeaf`) | `SRof fqValAbs` / `SRof fqCanonAbs` |
| `SRcarry` (`RunBlockCorres`) | `SRcarryOf (pi bvAbs)` |
| `SRcarryLimbs names` (`RunBlockCorres`) | `SRcarryOf ((pi bvAbs).pair (limbWindowAbs names))` |
| `LimbStoreRefines` (ParamTransfer) | `SRpi (limbAbs p hp)` |
| `MultiLimbStoreRefines` (ParamTransfer) | `SRpi (multiLimbAbs n p hp)` |

The ascent leaves are stated once over `SRof V` / `SRcarryOf (pi V)` and the
value content of a carrier enters through a square hypothesis; the bespoke leaves
`corres_setScalar_NT`, `corres_setExpr`, `corres_setExprBitwise`,
`corres_setExpr_fqAdd`, `corresJ_sbb`, `corresJ_adc` are recovered by supplying
the square of their carrier.

## Main results

* `ValueAbs`, with the combinators `graph`, `refl`, `sub`, `comp`, `pi`, `pair`.
* The carrier instances `wordAbs`, `bvAbs`, `fqValAbs`, `fqCanonAbs`, `limbAbs`,
  `multiLimbAbs`, `natModAbs`, `limbWindowAbs`, `limbWindowFieldAbs`, and
  `limbWindowFieldAbs_refines_iff` relating the register window to the
  multi-limb split surjection `multiLimbFieldParam`.
* The store relations `SRof`, `SRpi`, `SRcarryOf` and the instance theorems
  `srwordNT_iff_srof`, `srwordBV_iff_srof`, `srfqVal_iff_srof`,
  `srfqCanon_iff_srof`, `srcarry_iff_srcarryOf`, `srcarryLimbs_iff_srcarryOf`,
  `limbStoreRefines_iff_srpi`, `multiLimbStoreRefines_iff_srpi`.
* The generic scalar leaves `corres_setScalar_of`, `corresH_setExpr_of`,
  `corres_setExpr_of`, and the recovered bespoke leaves
  `corres_setScalar_NT_of_abs`, `corres_setExpr_of_abs`,
  `corres_setExprBitwise_of_abs`, `corres_setExpr_fqAdd_of_abs`.
* The generic `runBlock` lifting `corresJ_lift` and the generic flag leaves
  `corresJ_sbb_of`, `corresJ_adc_of`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The value abstraction -/

/-- A value abstraction from a concrete carrier `C` to an abstract carrier `A`: an
    encoding `enc` and the refinement predicate `Refines` a state relation reads
    pointwise. `Refines` defaults to the graph of `enc`; the law `enc_of_refines`
    keeps every `Refines` a subgraph of the encoding. -/
structure ValueAbs (C A : Type) where
  /-- The encoding of a concrete value. -/
  enc : C → A
  /-- The refinement predicate between a concrete and an abstract value. -/
  Refines : C → A → Prop := fun c a => enc c = a
  /-- `Refines` is a subgraph of the encoding. -/
  enc_of_refines : ∀ {c : C} {a : A}, Refines c a → enc c = a := by
    intro c a h; exact h

namespace ValueAbs

variable {C A B : Type}

/-- An abstraction is functional: one concrete value refines at most one abstract
    value. -/
theorem refines_functional (V : ValueAbs C A) {c : C} {a a' : A}
    (h : V.Refines c a) (h' : V.Refines c a') : a = a' := by
  rw [← V.enc_of_refines h, ← V.enc_of_refines h']

/-- The abstraction whose refinement is exactly the graph of `enc`. -/
def graph (enc : C → A) : ValueAbs C A := { enc }

theorem graph_refines_iff (enc : C → A) (c : C) (a : A) :
    (graph enc).Refines c a ↔ enc c = a := Iff.rfl

/-- The identity abstraction: the abstract value is the concrete value. -/
def refl (C : Type) : ValueAbs C C := graph fun c => c

theorem refl_refines_iff (c a : C) : (refl C).Refines c a ↔ c = a := Iff.rfl

/-- Restriction by a predicate on the concrete representative: `Refines` holds
    only where `P` does. -/
def sub (V : ValueAbs C A) (P : C → Prop) : ValueAbs C A where
  enc := V.enc
  Refines c a := P c ∧ V.Refines c a
  enc_of_refines h := V.enc_of_refines h.2

theorem sub_refines_iff (V : ValueAbs C A) (P : C → Prop) (c : C) (a : A) :
    (V.sub P).Refines c a ↔ P c ∧ V.Refines c a := Iff.rfl

/-- The restriction refines into the unrestricted abstraction. -/
theorem refines_of_sub (V : ValueAbs C A) (P : C → Prop) {c : C} {a : A}
    (h : (V.sub P).Refines c a) : V.Refines c a := h.2

/-- Composition through an intermediate carrier. -/
def comp (V : ValueAbs C B) (W : ValueAbs B A) : ValueAbs C A where
  enc c := W.enc (V.enc c)
  Refines c a := ∃ b, V.Refines c b ∧ W.Refines b a
  enc_of_refines := by
    rintro c a ⟨b, hb, hw⟩
    rw [V.enc_of_refines hb, W.enc_of_refines hw]

theorem comp_refines_iff (V : ValueAbs C B) (W : ValueAbs B A) (c : C) (a : A) :
    (V.comp W).Refines c a ↔ ∃ b, V.Refines c b ∧ W.Refines b a := Iff.rfl

/-- Pointwise abstraction of an indexed family (a store). -/
def pi {I : Type} (V : ValueAbs C A) : ValueAbs (I → C) (I → A) where
  enc f i := V.enc (f i)
  Refines f g := ∀ i, V.Refines (f i) (g i)
  enc_of_refines h := funext fun i => V.enc_of_refines (h i)

theorem pi_refines_iff {I : Type} (V : ValueAbs C A) (f : I → C) (g : I → A) :
    (pi V).Refines f g ↔ ∀ i, V.Refines (f i) (g i) := Iff.rfl

/-- Fan-in: two abstractions read off the same concrete value. -/
def pair (V : ValueAbs C A) (W : ValueAbs C B) : ValueAbs C (A × B) where
  enc c := (V.enc c, W.enc c)
  Refines c p := V.Refines c p.1 ∧ W.Refines c p.2
  enc_of_refines h := Prod.ext (V.enc_of_refines h.1) (W.enc_of_refines h.2)

theorem pair_refines_iff (V : ValueAbs C A) (W : ValueAbs C B) (c : C) (p : A × B) :
    (V.pair W).Refines c p ↔ V.Refines c p.1 ∧ W.Refines c p.2 := Iff.rfl

end ValueAbs

/-! ## The carrier instances -/

/-- The 64-bit word as `ZMod 2^64` through `wEnc`. -/
def wordAbs : ValueAbs (BitVec 64) (ZMod (2 ^ 64)) := ValueAbs.graph wEnc

/-- The 64-bit word kept as a `BitVec 64`. -/
def bvAbs : ValueAbs (BitVec 64) (BitVec 64) := ValueAbs.refl (BitVec 64)

/-- The ML-KEM coefficient slot as `ZMod 3329` through `fqEnc`, without a range
    condition. -/
def fqValAbs : ValueAbs (BitVec 64) (ZMod 3329) := ValueAbs.graph fqEnc

/-- The ML-KEM coefficient slot as `ZMod 3329` with a canonical representative
    (`w.toNat < 3329`). -/
def fqCanonAbs : ValueAbs (BitVec 64) (ZMod 3329) :=
  fqValAbs.sub fun w => w.toNat < 3329

/-- The single limb as `ZMod p` through the split surjection `limbFieldParam`. -/
def limbAbs (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64) : ValueAbs (BitVec 64) (ZMod p) where
  enc w := (w.toNat : ZMod p)
  Refines := (limbFieldParam p hp).R
  enc_of_refines h := h

/-- The limb array as `ZMod p` through the multi-limb split surjection
    `multiLimbFieldParam`. -/
def multiLimbAbs (n p : ℕ) [NeZero p] (hp : p ≤ 2 ^ (64 * n)) :
    ValueAbs (Fin n → BitVec 64) (ZMod p) where
  enc l := (Transfer.Param.limbVal n l : ZMod p)
  Refines := (Transfer.Param.multiLimbFieldParam n p hp).R
  enc_of_refines h := h

/-- A natural number as its residue in `ZMod p`. -/
def natModAbs (p : ℕ) : ValueAbs ℕ (ZMod p) := ValueAbs.graph fun v => (v : ZMod p)

/-- A register window, named by `names` in little-endian order, as its base-`2^64`
    recomposition `limbVal`. -/
def limbWindowAbs (names : List String) : ValueAbs (String → BitVec 64) ℕ :=
  ValueAbs.graph fun σ => limbVal (names.map σ)

/-- A register window as its residue in `ZMod p`. -/
def limbWindowFieldAbs (names : List String) (p : ℕ) :
    ValueAbs (String → BitVec 64) (ZMod p) :=
  (limbWindowAbs names).comp (natModAbs p)

/-- The list recomposition `limbVal` agrees with ParamTransfer's `Fin`-indexed
    `Transfer.Param.limbVal` on `List.ofFn`. -/
theorem limbVal_ofFn : ∀ (n : ℕ) (f : Fin n → BitVec 64),
    limbVal (List.ofFn f) = Transfer.Param.limbVal n f
  | 0, _ => by simp [limbVal]
  | n + 1, f => by
      rw [List.ofFn_succ, limbVal, Transfer.Param.limbVal_succ, limbVal_ofFn n]
      rfl

/-- The register-window field abstraction is the multi-limb split surjection
    `multiLimbFieldParam` read on the window `fun i => σ names[i]`. -/
theorem limbWindowFieldAbs_refines_iff (names : List String) (p : ℕ) [NeZero p]
    (hp : p ≤ 2 ^ (64 * names.length)) (σ : String → BitVec 64) (x : ZMod p) :
    (limbWindowFieldAbs names p).Refines σ x ↔
      (multiLimbAbs names.length p hp).Refines (fun i => σ names[i]) x := by
  have hmap : names.map σ = List.ofFn (fun i : Fin names.length => σ names[i]) :=
    List.ext_getElem (by simp) (fun i h1 h2 => by simp)
  show (∃ b, limbVal (names.map σ) = b ∧ (b : ZMod p) = x) ↔
    ((Transfer.Param.limbVal names.length (fun i => σ names[i]) : ZMod p) = x)
  rw [hmap, limbVal_ofFn]
  constructor
  · rintro ⟨b, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

/-! ## The generic store relations -/

/-- The scalar-environment store relation of an abstraction: every non-temp name
    holds a `.sword 64` word refining the abstract value. The shape of `SRwordNT`. -/
def SRof {A : Type} (V : ValueAbs (BitVec 64) A) (env : SEnvScalar) (a : String → A) : Prop :=
  ∀ x, ¬ isTmpName x → ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ V.Refines w (a x)

/-- The total pointwise store relation of an abstraction over an index type. -/
def SRpi {I C A : Type} (V : ValueAbs C A) (s : I → C) (s' : I → A) : Prop :=
  ∀ i, V.Refines (s i) (s' i)

/-- The `JState` store relation of an abstraction of the register file, with the
    carry flag carried alongside. The shape of `SRcarry`. -/
def SRcarryOf {A : Type} (V : ValueAbs (String → BitVec 64) A) (st : JState 64)
    (a : A × Bool) : Prop :=
  V.Refines st.regs a.1 ∧ st.flagB (·.cf) = a.2

/-- The state relation `SRcarryOf (ValueAbs.pi bvAbs)` is non-empty. -/
theorem srcarryOf_satisfiable :
    ∃ st, ∃ a : (String → BitVec 64) × Bool, SRcarryOf (ValueAbs.pi bvAbs) st a := by
  refine ⟨{ regs := fun _ => 0, flags := { cf := some false, of := none } },
    (fun _ => 0, false), ?_⟩
  exact ⟨fun _ => rfl, rfl⟩

theorem srwordNT_iff_srof (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) :
    SRwordNT env a ↔ SRof wordAbs env a := Iff.rfl

theorem srwordBV_iff_srof (env : SEnvScalar) (a : String → BitVec 64) :
    SRwordBV env a ↔ SRof bvAbs env a := by
  constructor
  · intro h x hx; exact ⟨a x, h x hx, rfl⟩
  · intro h x hx
    obtain ⟨w, hw, hwa⟩ := h x hx
    rw [show w = a x from hwa] at hw
    exact hw

theorem srfqVal_iff_srof (env : SEnvScalar) (a : String → ZMod 3329) :
    SRfqVal env a ↔ SRof fqValAbs env a := Iff.rfl

theorem srfqCanon_iff_srof (env : SEnvScalar) (a : String → ZMod 3329) :
    SRfqCanon env a ↔ SRof fqCanonAbs env a := Iff.rfl

theorem srcarry_iff_srcarryOf (st : JState 64) (a : ACarry) :
    SRcarry st a ↔ SRcarryOf (ValueAbs.pi bvAbs) st (a.regs, a.cf) := Iff.rfl

theorem srcarryLimbs_iff_srcarryOf (names : List String) (st : JState 64) (a : ACarryLimbs) :
    SRcarryLimbs names st a ↔
      SRcarryOf ((ValueAbs.pi bvAbs).pair (limbWindowAbs names)) st ((a.regs, a.val), a.cf) :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩

theorem limbStoreRefines_iff_srpi (V : Type) (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    (s : V → BitVec 64) (s' : V → ZMod p) :
    LimbStoreRefines V p hp s s' ↔ SRpi (limbAbs p hp) s s' := by
  constructor
  · intro h v; exact h v v rfl
  · rintro h v _ rfl; exact h v

theorem multiLimbStoreRefines_iff_srpi (E : Type) (n p : ℕ) [NeZero p]
    (hp : p ≤ 2 ^ (64 * n)) (S : E → (Fin n → BitVec 64)) (X : E → ZMod p) :
    Transfer.Param.MultiLimbStoreRefines E n p hp S X ↔ SRpi (multiLimbAbs n p hp) S X := by
  constructor
  · intro h e; exact h e e rfl
  · rintro h e _ rfl; exact h e

/-! ## The generic scalar leaves over `SRof` -/

/-- The literal-assignment leaf over any abstraction: `RScalarSet name n` sets the
    abstract `name` to a value `v` refined by the literal word. -/
theorem corres_setScalar_of {A : Type} (V : ValueAbs (BitVec 64) A) (name : String)
    (n : Nat) {v : A} (hv : V.Refines (BitVec.ofNat 64 n) v) :
    Corres (SRof V) (fun _ => True)
      (fun a s => if s = name then v else a s) (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x hnt
  by_cases hx : x = name
  · subst hx
    refine ⟨BitVec.ofNat 64 n, by simp [SEnvScalar.upd], ?_⟩
    dsimp only; rw [ite_eq_left rfl]; exact hv
  · obtain ⟨w, hw, hwn⟩ := hSR x hnt
    refine ⟨w, by simp [SEnvScalar.upd, hx, hw], ?_⟩
    dsimp only; rw [ite_eq_right hx]; exact hwn

/-- The expression-assignment leaf over a pair of abstractions: from a store
    refined through `Vi`, `RScalarSetExpr x e` (source-clean `e`) lands in a store
    refined through `Vo` whose `x` is `F a`, provided the concrete evaluation refines
    `F a` on every `Vi`-refined reader (`hF`) and `Vi` refines into `Vo` on the
    untouched names (`hle`). Progress is `semLowerSExpr_ok'`. -/
theorem corresH_setExpr_of {A : Type} (Vi Vo : ValueAbs (BitVec 64) A)
    (hle : ∀ {w : BitVec 64} {v : A}, Vi.Refines w v → Vo.Refines w v)
    (x : String) (e : SExpr) (he : srcClean e) (F : (String → A) → A)
    (hF : ∀ (β : String → BitVec 64) (a : String → A),
      (∀ y, ¬ isTmpName y → Vi.Refines (β y) (a y)) → Vo.Refines (SExpr.evalBV β e) (F a)) :
    CorresH (SRof Vi) (SRof Vo) (fun _ => True)
      (fun a s => if s = x then F a else a s) (.RScalarSetExpr x e) := by
  intro env a hSR _
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    obtain ⟨w, hw, _⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e) he
  have hval : Vo.Refines (SExpr.evalBV (envReader env) e) (F a) := by
    apply hF
    intro y hnt
    obtain ⟨w, hw, hwe⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    rw [hr]; exact hwe
  refine ⟨env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = x
    · refine ⟨SExpr.evalBV (envReader env) e, ?_, ?_⟩
      · simp only [SEnvScalar.upd, ite_eq_left hyx]
      · dsimp only; rw [ite_eq_left hyx]; exact hval
    · obtain ⟨w, hw, hwe⟩ := hSR y hnt
      refine ⟨w, ?_, ?_⟩
      · simp only [SEnvScalar.upd, ite_eq_right hyx]
        rw [hotb y (Or.inl hnt)]; exact hw
      · dsimp only; rw [ite_eq_right hyx]; exact hle hwe

/-- The homogeneous expression-assignment leaf: `corresH_setExpr_of` at `Vi = Vo`. -/
theorem corres_setExpr_of {A : Type} (V : ValueAbs (BitVec 64) A)
    (x : String) (e : SExpr) (he : srcClean e) (F : (String → A) → A)
    (hF : ∀ (β : String → BitVec 64) (a : String → A),
      (∀ y, ¬ isTmpName y → V.Refines (β y) (a y)) → V.Refines (SExpr.evalBV β e) (F a)) :
    Corres (SRof V) (fun _ => True)
      (fun a s => if s = x then F a else a s) (.RScalarSetExpr x e) :=
  corresH_setExpr_of V V (fun h => h) x e he F hF

/-! ## The bespoke scalar leaves as instances -/

/-- `corres_setScalar_NT` recovered from `corres_setScalar_of` at `wordAbs`. -/
theorem corres_setScalar_NT_of_abs (name : String) (n : Nat) :
    Corres SRwordNT (fun _ => True)
      (fun a s => if s = name then (n : ZMod (2 ^ 64)) else a s)
      (.RScalarSet name n) :=
  corres_setScalar_of wordAbs name n
    (by simp [wordAbs, ValueAbs.graph, wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod])

/-- `corres_setExpr` recovered from `corres_setExpr_of` at `wordAbs`; the square is
    `wEnc_evalBV_evalZMod`. -/
theorem corres_setExpr_of_abs (x : String) (e : SExpr) (he : IsArithClean e) :
    Corres SRwordNT (fun _ => True)
      (fun a s => if s = x then evalZMod a e else a s)
      (.RScalarSetExpr x e) :=
  corres_setExpr_of wordAbs x e (isArithClean_srcClean e he) (fun a => evalZMod a e)
    (fun β a h => wEnc_evalBV_evalZMod β a h e he)

/-- `corres_setExprBitwise` recovered from `corres_setExpr_of` at `bvAbs`; the
    square is reader agreement `evalBV_congr_on`. -/
theorem corres_setExprBitwise_of_abs (x : String) (e : SExpr) (he : IsWordClean e) :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = x then SExpr.evalBV a e else a s)
      (.RScalarSetExpr x e) := by
  intro env a hSR hP
  exact corres_setExpr_of bvAbs x e (isWordClean_srcClean e he) (fun a => SExpr.evalBV a e)
    (fun β a h => evalBV_congr_on (fun _ => True) β a e (fun s _ hns => h s hns)
      (varsBoundIn_true e) (isWordClean_srcClean e he))
    env a ((srwordBV_iff_srof env a).mp hSR) hP
    |>.imp fun env' ⟨hs, hr⟩ => ⟨hs, (srwordBV_iff_srof env' _).mpr hr⟩

/-- `corres_setExpr_fqAdd` recovered from `corresH_setExpr_of` at
    `fqCanonAbs → fqValAbs`; the square is `fqEnc_add_of_canonical`. -/
theorem corres_setExpr_fqAdd_of_abs (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName) :
    CorresH SRfqCanon SRfqVal (fun _ => True)
      (fun φ s => if s = rName then φ aName + φ bName else φ s)
      (.RScalarSetExpr rName (.SAdd (.SVar aName) (.SVar bName))) :=
  corresH_setExpr_of fqCanonAbs fqValAbs (fun h => h.2) rName
    (.SAdd (.SVar aName) (.SVar bName)) ⟨hna, hnb⟩ (fun φ => φ aName + φ bName)
    (fun β a h => by
      obtain ⟨hlta, hea⟩ := h aName hna
      obtain ⟨hltb, heb⟩ := h bName hnb
      show fqEnc (β aName + β bName) = a aName + a bName
      rw [fqEnc_add_of_canonical _ _ hlta hltb]
      exact congrArg₂ (· + ·) hea heb)

/-! ## The generic `runBlock` leaves over `SRcarryOf (pi V)` -/

/-- A `CorresJ` over the identity relation `SRcarry` lifts to any pointwise
    abstraction `pi V` of the register file, given the abstract step `fstep` squares
    with the concrete step on `V`-refined registers (`hsq`). The lift reuses the
    identity-instance proof. -/
theorem corresJ_lift {A : Type} (V : ValueAbs (BitVec 64) A) {step : ACarry → ACarry}
    {c : List (JInstr 64)} (h : CorresJ SRcarry (fun _ => True) step c)
    (fstep : (String → A) × Bool → (String → A) × Bool)
    (hsq : ∀ (ρ : String → BitVec 64) (b : Bool) (α : String → A),
      (∀ r, V.Refines (ρ r) (α r)) →
        (∀ r, V.Refines ((step ⟨ρ, b⟩).regs r) ((fstep (α, b)).1 r)) ∧
          (step ⟨ρ, b⟩).cf = (fstep (α, b)).2) :
    CorresJ (SRcarryOf (ValueAbs.pi V)) (fun _ => True) fstep c := by
  intro st a hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  obtain ⟨hr', hcf'⟩ := h st ⟨st.regs, a.2⟩ ⟨fun _ => rfl, hcf⟩ trivial
  obtain ⟨h1, h2⟩ := hsq st.regs a.2 a.1 hreg
  refine ⟨fun r => ?_, ?_⟩
  · rw [hr' r]; exact h1 r
  · rw [hcf', h2]

/-- The subtract-with-borrow leaf over any pointwise abstraction: the data square
    `hdata` and the borrow square `hcf` of the carrier give `sbb dst src` over
    `SRcarryOf (pi V)`. -/
theorem corresJ_sbb_of {A : Type} (V : ValueAbs (BitVec 64) A) (dst src : String)
    (fdata : A → A → Bool → A) (fcf : A → A → Bool → Bool)
    (hdata : ∀ (x y : BitVec 64) (b : Bool) (ax ay : A), V.Refines x ax → V.Refines y ay →
      V.Refines (sub_borrow x y (if b then 1 else 0)) (fdata ax ay b))
    (hcf : ∀ (x y : BitVec 64) (b : Bool) (ax ay : A), V.Refines x ax → V.Refines y ay →
      decide (((x.toNat : Int) - y.toNat - ((if b then 1 else 0 : Nat) : Int) < 0))
        = fcf ax ay b) :
    CorresJ (SRcarryOf (ValueAbs.pi V)) (fun _ => True)
      (fun a => (fun r => if r = dst then fdata (a.1 dst) (a.1 src) a.2 else a.1 r,
        fcf (a.1 dst) (a.1 src) a.2))
      [.sbb dst (.reg src)] := by
  refine corresJ_lift V (corresJ_sbb dst src) _ ?_
  intro ρ b α hρ
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r = dst
    · subst hr
      simp only [sbbStep, ite_true]
      exact hdata _ _ _ _ _ (hρ _) (hρ _)
    · simp only [sbbStep, ite_eq_right hr]
      exact hρ r
  · simp only [sbbStep]
    exact hcf _ _ _ _ _ (hρ _) (hρ _)

/-- The add-with-carry leaf over any pointwise abstraction: the data square `hdata`
    and the carry square `hcf` of the carrier give `adc dst src` over
    `SRcarryOf (pi V)`. -/
theorem corresJ_adc_of {A : Type} (V : ValueAbs (BitVec 64) A) (dst src : String)
    (fdata : A → A → Bool → A) (fcf : A → A → Bool → Bool)
    (hdata : ∀ (x y : BitVec 64) (b : Bool) (ax ay : A), V.Refines x ax → V.Refines y ay →
      V.Refines (add_carry x y (if b then 1 else 0)) (fdata ax ay b))
    (hcf : ∀ (x y : BitVec 64) (b : Bool) (ax ay : A), V.Refines x ax → V.Refines y ay →
      decide (2 ^ 64 ≤ x.toNat + y.toNat + (if b then 1 else 0)) = fcf ax ay b) :
    CorresJ (SRcarryOf (ValueAbs.pi V)) (fun _ => True)
      (fun a => (fun r => if r = dst then fdata (a.1 dst) (a.1 src) a.2 else a.1 r,
        fcf (a.1 dst) (a.1 src) a.2))
      [.adc dst (.reg src)] := by
  refine corresJ_lift V (corresJ_adc dst src) _ ?_
  intro ρ b α hρ
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r = dst
    · subst hr
      simp only [adcStep, ite_true]
      exact hdata _ _ _ _ _ (hρ _) (hρ _)
    · simp only [adcStep, ite_eq_right hr]
      exact hρ r
  · simp only [adcStep]
    exact hcf _ _ _ _ _ (hρ _) (hρ _)

/-- `corresJ_sbb` is the `bvAbs` instance of `corresJ_sbb_of`. -/
example (dst src : String) :
    CorresJ (SRcarryOf (ValueAbs.pi bvAbs)) (fun _ => True)
      (fun a => (fun r => if r = dst then sub_borrow (a.1 dst) (a.1 src) (if a.2 then 1 else 0)
          else a.1 r,
        decide (((a.1 dst).toNat : Int) - (a.1 src).toNat
          - ((if a.2 then 1 else 0 : Nat) : Int) < 0)))
      [.sbb dst (.reg src)] :=
  corresJ_sbb_of bvAbs dst src
    (fun ax ay b => sub_borrow ax ay (if b then 1 else 0))
    (fun ax ay b => decide (((ax.toNat : Int) - ay.toNat - ((if b then 1 else 0 : Nat) : Int) < 0)))
    (fun x y b ax ay hx hy => by
      show sub_borrow x y (if b then 1 else 0) = sub_borrow ax ay (if b then 1 else 0)
      rw [show x = ax from hx, show y = ay from hy])
    (fun x y b ax ay hx hy => by
      rw [show x = ax from hx, show y = ay from hy])

end CatCrypt.Crypto.SecureCompilation.Ascent
