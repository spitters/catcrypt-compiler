/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.HawkMulEmit
import CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayRealization

/-!
# HAWK ring-multiply: the proof-model `Com` kernel denotes the spec

`HawkMulEmit.hawkMulCom` is the **proof-model** `Com jasminDialect`
straight-line kernel for the HAWK-256 negacyclic ring multiply over
`Z/1024[x]/(x^16 + 1)` (512 `regArith` bindings: schoolbook `mul`, accumulating
`add`/`sub` for the `x^N=-1` sign, and a final `& 1023` field mask). The
*deployed* artifact is the front-generated `HawkMulEmit.hawkMulFrontCom`
(rendered by `HAWK/HawkMulEmit`); this model carries the universal
verification content for the same spec.
`HawkMul4WayRealization.hawkNegacyclicMul` is the abstract spec over
`ZMod 1024`. This module proves they agree: the **denotation** of the model
Com kernel computes the negacyclic product.

## Main result

`hawkMulCom_denote_spec` : for every lane pair `a b : HawkLane`,

  `hawkMulCom.denote (encode a b) = embZ (hawkNegacyclicMul a b ⟨N-1⟩)`

i.e. denoting the emitted kernel on the encoded input gives the embedded
negacyclic product at the returned coefficient. This is a **full `N = 16`** tie:
the per-coefficient lemma `final_outSlot_spec` establishes it for **every**
`k < N` (the kernel returns `out[N-1]`; the slot-level result covers all 16
output coefficients), so it is not a degenerate or single-coefficient instance.

## Proof architecture (the Jasmin denotation is used once)

1. **Slot-map abstraction** (`slotMap`, `Respects`): a builder state `+` valuation
   is described by `Fin M → BitVec 32`. The Jasmin dialect denotation enters
   exactly once, in `emitOp_slotMap` (one binding = one functional slot update);
   every other step is pure `BitVec`/`Function.update` reasoning.
2. **Pure models** (`coeffsModel`/`tailModel`/`maskModel`) of the recursive CPS
   builders, lifted to the denotation via `Respects` (`hawkMulCom_denote`
   collapses the 512-binding denotation to `maskModel 0 ∘ coeffsModel 0`).
3. **BitVec convolution** (`bvAccum`/`bvTerm`): the models accumulate the
   negacyclic schoolbook product; slot-disjointness lemmas show inputs are never
   clobbered.
4. **`ZMod 1024` bridge** (`φ`): the mask `& 1023` ↔ `mod 1024` reduction.
   `φ x = (x.toNat : ZMod 1024)` is a ring map (because `1024 ∣ 2^32`, so the
   `2^32` wrap is invisible mod `1024`), sends `embZ z ↦ z`, is `& 1023`-invariant
   (`φ_mask` — the key mask↔mod bridge, via `BitVec.toNat_and` +
   `Nat.and_two_pow_sub_one_eq_mod`), and carries the BitVec convolution to the
   `Finset.sum` of `negaTerm`s, i.e. `hawkNegacyclicMul`.

## Scope (boundary — read this)

What is proved here is the **Com-IR denotation ⟷ abstract-spec** tie:
`hawkMulCom.denote = hawkNegacyclicMul` (mod the `& 1023` field reduction), for
the proof-model Com. This is *not* a proof about the emitted x86 `.s` bytes,
and the deployed `.s` renders the front-generated `hawkMulFrontCom` (gated by
`HawkMulEmit.hawk_denote_spec` against the same negacyclic reference on sample
vectors). The emitted x86 bytes vs the reference remain **KAT-anchored**
(`bench/hawk_compare/hawk_mul_kat.c` / `hawk_mul_4way_kat.c`). We tie the model
Com denotation; we do not claim the x86 bytes are proven.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.HawkMulComDenoteTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.HawkMulEmit
open CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayRealization
open CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit (Zq1024 HawkLane)

local notation "BState" => HawkMulEmit.BState
local notation "M" => HawkMulEmit.M
local notation "emitOp" => HawkMulEmit.emitOp
local notation "headVar" => HawkMulEmit.headVar

/-- The **semantic slot map** of a builder state under a valuation: slot `i`
    holds the looked-up value of the variable that `st` assigns to slot `i`. This
    abstracts away the growing context — a `(st, V)` pair is fully described by
    `slotMap st V : Fin M → BitVec 32`. -/
def slotMap {Γ : Ctxt jasminDialect} (st : BState Γ) (V : Ctxt.Valuation Γ) :
    Fin M → BitVec 32 :=
  fun i => (st.st i).lookup V

/-- **The one-op slot-map step.** Denoting `emitOp st op dst a b k` equals denoting
    the continuation at the extended state, whose slot map is `slotMap st V` with
    slot `dst` updated to `op.apply (slotMap … a) (slotMap … b)`. This is the only
    fact about the Jasmin denotation the convolution tie needs: each binding is a
    pure functional update of one slot. -/
theorem emitOp_slotMap {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin M)
    (k : {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t)
    (V : Ctxt.Valuation Γ) :
    (emitOp st op dst a b k).denote V
      = (k { st := fun i => if i = dst then headVar Γ else (st.st i).there }).denote
          (V.extend (JasminBinOp.apply op (slotMap st V a) (slotMap st V b))) := by
  unfold HawkMulEmit.emitOp slotMap
  rfl

/-- The slot map of the state `emitOp` hands to its continuation is exactly the
    functional update `Function.update (slotMap st V) dst (op.apply …)`. Combined
    with `emitOp_slotMap`, this says one binding performs one slot update. -/
theorem slotMap_emitOp_state {Γ : Ctxt jasminDialect}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin M) (V : Ctxt.Valuation Γ) :
    slotMap (Γ := r32 :: Γ)
        { st := fun i => if i = dst then headVar Γ else (st.st i).there }
        (V.extend (JasminBinOp.apply op (slotMap st V a) (slotMap st V b)))
      = Function.update (slotMap st V) dst
          (JasminBinOp.apply op (slotMap st V a) (slotMap st V b)) := by
  funext i
  unfold slotMap HawkMulEmit.headVar Ctxt.Valuation.extend
  by_cases h : i = dst
  · subst h
    rw [Function.update_self]
    simp only [reduceIte]
    rfl
  · simp only [if_neg h, Function.update_of_ne h]
    rfl

/-! ## 2. Slot-map–respecting continuations

The CPS builders (`emitOp`, `emitCoeff`, `emitMasks`, …) read state only through
`st.st <slot>` and the dialect denotation reads the bound values only through the
valuation. Hence the denotation of any builder applied to `(st, V)` depends on
the pair only through `slotMap st V`. We capture this as `Respects k f`: the
denotation of continuation `k` at any `(st, V)` is the pure function `f` applied
to the slot map. Every builder then transforms `f` by a pure `Fin M → BitVec 32`
update, with the Jasmin denotation used exactly once (in `emitOp_slotMap`). -/

/-- `Respects k f`: the denotation of the polymorphic continuation `k` at any
    state `(st, V)` is `f (slotMap st V)` — i.e. `k`'s denotation factors through
    the slot map. -/
def Respects {t : JasminTy} (k : HawkMulEmit.Cont t)
    (f : (Fin M → BitVec 32) → ⟦t⟧) : Prop :=
  ∀ (Γ : Ctxt jasminDialect) (st : BState Γ) (V : Ctxt.Valuation Γ),
    (k (Γ' := Γ) st).denote V = f (slotMap st V)

/-- `.ret (st.st (outSlot r))` respects `fun σ => σ (outSlot r)`. -/
theorem respects_ret (r : Nat) :
    Respects (t := r32) (fun st => .ret (st.st (HawkMulEmit.outSlot r)))
      (fun σ => σ (HawkMulEmit.outSlot r)) := by
  intro Γ st V; rfl

/-- **`emitOp` pure-step.** If the continuation respects `f`, then
    `emitOp · op dst a b k` respects `f` precomposed with the single-slot update
    `σ ↦ update σ dst (op.apply (σ a) (σ b))`. The Jasmin denotation enters here
    (via `emitOp_slotMap` + `slotMap_emitOp_state`) and nowhere else. -/
theorem respects_emitOp {t : JasminTy} (op : JasminBinOp) (dst a b : Fin M)
    (k : HawkMulEmit.Cont t) (f : (Fin M → BitVec 32) → ⟦t⟧) (hk : Respects k f) :
    Respects (fun st => emitOp st op dst a b k)
      (fun σ => f (Function.update σ dst (JasminBinOp.apply op (σ a) (σ b)))) := by
  intro Γ st V
  rw [emitOp_slotMap, hk, slotMap_emitOp_state]

/-! ## 3. Pure slot-map models of the recursive builders

For each builder we give a pure `(Fin M → BitVec 32) → (Fin M → BitVec 32)`
model and prove a `Respects`-lifting lemma by well-founded induction, reusing
`respects_emitOp`. The Jasmin denotation is never touched again. -/

local notation "aSlot" => HawkMulEmit.aSlot
local notation "bSlot" => HawkMulEmit.bSlot
local notation "outSlot" => HawkMulEmit.outSlot
local notation "scrSlot" => HawkMulEmit.scrSlot
local notation "maskConstSlot" => HawkMulEmit.maskConstSlot
local notation "partner" => HawkMulEmit.partner
local notation "emitCoeffTail" => HawkMulEmit.emitCoeffTail
local notation "emitCoeff" => HawkMulEmit.emitCoeff
local notation "emitCoeffs" => HawkMulEmit.emitCoeffs
local notation "emitMasks" => HawkMulEmit.emitMasks

/-- Pure model of `emitMasks`: mask output slots `k … N-1` with the mask-constant
    slot (`& 1023`). -/
def maskModel : Nat → (Fin M → BitVec 32) → (Fin M → BitVec 32)
  | k, σ =>
    if k < HawkMulEmit.N then
      maskModel (k + 1)
        (Function.update σ (outSlot k)
          (JasminBinOp.apply .and (σ (outSlot k)) (σ maskConstSlot)))
    else σ
  termination_by k => HawkMulEmit.N - k

/-- The `emitMasks k`-continuation, packaged as a `Cont` (controls the implicit
    context binder so the `Respects` lemmas chain cleanly). -/
@[reducible] def masksCont {t : JasminTy} (k : Nat) (kont : HawkMulEmit.Cont t) :
    HawkMulEmit.Cont t := fun st => emitMasks k st kont

/-- `masksCont k kont` respects `f ∘ maskModel k`. -/
theorem respects_emitMasks {t : JasminTy} (k : Nat)
    (kont : HawkMulEmit.Cont t) (f : (Fin M → BitVec 32) → ⟦t⟧)
    (hk : Respects kont f) :
    Respects (masksCont k kont) (fun σ => f (maskModel k σ)) := by
  intro Γ st V
  show (emitMasks k st kont).denote V = f (maskModel k (slotMap st V))
  by_cases hkN : k < HawkMulEmit.N
  · have ih := respects_emitMasks (k + 1) kont f hk
    have hstep := respects_emitOp (t := t) .and (outSlot k) (outSlot k) maskConstSlot
      (masksCont (k + 1) kont) _ ih
    have hE : (emitMasks k st kont) =
        emitOp st .and (outSlot k) (outSlot k) maskConstSlot (masksCont (k + 1) kont) := by
      conv_lhs => rw [emitMasks.eq_def]
      simp only [hkN, if_true]
    rw [hE]
    have := hstep Γ st V
    rw [this]
    conv_rhs => rw [maskModel.eq_def]
    simp only [hkN, if_true]
  · have hE : (emitMasks k st kont) = kont st := by
      conv_lhs => rw [emitMasks.eq_def]; simp only [hkN, if_false]
    have hM : maskModel k (slotMap st V) = slotMap st V := by
      conv_lhs => rw [maskModel.eq_def]; simp only [hkN, if_false]
    rw [hE, hk Γ st V, hM]
termination_by HawkMulEmit.N - k

/-! ### Pure model + lifting for the accumulation builders -/

/-- Pure model of `emitCoeffTail k i`: for each term index `i … N-1`, write
    `scratch = a[i]·b[partner k i]` then accumulate it into `out[k]` with the
    negacyclic sign (`+` if `i ≤ k`, `−` if `i > k`). -/
def tailModel (k : Nat) : Nat → (Fin M → BitVec 32) → (Fin M → BitVec 32)
  | i, σ =>
    if i < HawkMulEmit.N then
      let σ1 := Function.update σ scrSlot
        (JasminBinOp.apply .mul (σ (aSlot i)) (σ (bSlot (partner k i))))
      let σ2 := Function.update σ1 (outSlot k)
        (JasminBinOp.apply (if i ≤ k then .add else .sub) (σ1 (outSlot k)) (σ1 scrSlot))
      tailModel k (i + 1) σ2
    else σ
  termination_by i => HawkMulEmit.N - i

/-- Pure model of `emitCoeff k`: the first product `out[k] = a[0]·b[partner k 0]`
    then the accumulating tail. -/
def coeffModel (k : Nat) (σ : Fin M → BitVec 32) : Fin M → BitVec 32 :=
  tailModel k 1
    (Function.update σ (outSlot k)
      (JasminBinOp.apply .mul (σ (aSlot 0)) (σ (bSlot (partner k 0)))))

/-- Pure model of `emitCoeffs k`: run `coeffModel` for output coeffs `k … N-1`. -/
def coeffsModel : Nat → (Fin M → BitVec 32) → (Fin M → BitVec 32)
  | k, σ =>
    if k < HawkMulEmit.N then coeffsModel (k + 1) (coeffModel k σ) else σ
  termination_by k => HawkMulEmit.N - k

/-- The `emitCoeffTail k i`-continuation as a `Cont`. -/
@[reducible] def tailCont {t : JasminTy} (k i : Nat) (kont : HawkMulEmit.Cont t) :
    HawkMulEmit.Cont t := fun st => emitCoeffTail k i st kont

/-- `tailCont k i kont` respects `f ∘ tailModel k i`. -/
theorem respects_emitCoeffTail {t : JasminTy} (k i : Nat)
    (kont : HawkMulEmit.Cont t) (f : (Fin M → BitVec 32) → ⟦t⟧)
    (hk : Respects kont f) :
    Respects (tailCont k i kont) (fun σ => f (tailModel k i σ)) := by
  intro Γ st V
  show (emitCoeffTail k i st kont).denote V = f (tailModel k i (slotMap st V))
  by_cases hiN : i < HawkMulEmit.N
  · -- one mul + one add/sub, then recurse on i+1
    have ih := respects_emitCoeffTail k (i + 1) kont f hk
    have hstep2 := respects_emitOp (t := t) (if i ≤ k then .add else .sub)
      (outSlot k) (outSlot k) scrSlot (tailCont k (i + 1) kont) _ ih
    have hstep1 := respects_emitOp (t := t) .mul scrSlot (aSlot i) (bSlot (partner k i)) _ _ hstep2
    have hE : (emitCoeffTail k i st kont) =
        emitOp st .mul scrSlot (aSlot i) (bSlot (partner k i)) (fun st1 =>
          emitOp st1 (if i ≤ k then .add else .sub) (outSlot k) (outSlot k) scrSlot (fun st2 =>
            emitCoeffTail k (i + 1) st2 kont)) := by
      conv_lhs => rw [HawkMulEmit.emitCoeffTail.eq_def]
      simp only [hiN, if_true]
    rw [hE]
    have := hstep1 Γ st V
    rw [this]
    conv_rhs => rw [tailModel.eq_def]
    simp only [hiN, if_true]
  · have hE : (emitCoeffTail k i st kont) = kont st := by
      conv_lhs => rw [HawkMulEmit.emitCoeffTail.eq_def]; simp only [hiN, if_false]
    have hM : tailModel k i (slotMap st V) = slotMap st V := by
      conv_lhs => rw [tailModel.eq_def]; simp only [hiN, if_false]
    rw [hE, hk Γ st V, hM]
termination_by HawkMulEmit.N - i

/-- The `emitCoeff k`-continuation as a `Cont`. -/
@[reducible] def coeffCont {t : JasminTy} (k : Nat) (kont : HawkMulEmit.Cont t) :
    HawkMulEmit.Cont t := fun st => emitCoeff k st kont

/-- `coeffCont k kont` respects `f ∘ coeffModel k`. -/
theorem respects_emitCoeff {t : JasminTy} (k : Nat)
    (kont : HawkMulEmit.Cont t) (f : (Fin M → BitVec 32) → ⟦t⟧)
    (hk : Respects kont f) :
    Respects (coeffCont k kont) (fun σ => f (coeffModel k σ)) := by
  intro Γ st V
  show (emitCoeff k st kont).denote V = f (coeffModel k (slotMap st V))
  have htail := respects_emitCoeffTail k 1 kont f hk
  have hstep := respects_emitOp (t := t) .mul (outSlot k) (aSlot 0) (bSlot (partner k 0))
    (tailCont k 1 kont) _ htail
  have hE : (emitCoeff k st kont) =
      emitOp st .mul (outSlot k) (aSlot 0) (bSlot (partner k 0))
        (fun st1 => emitCoeffTail k 1 st1 kont) := by
    rw [HawkMulEmit.emitCoeff]
  rw [hE]
  have := hstep Γ st V
  rw [this]
  rfl

/-- The `emitCoeffs k`-continuation as a `Cont`. -/
@[reducible] def coeffsCont {t : JasminTy} (k : Nat) (kont : HawkMulEmit.Cont t) :
    HawkMulEmit.Cont t := fun st => emitCoeffs k st kont

/-- `coeffsCont k kont` respects `f ∘ coeffsModel k`. -/
theorem respects_emitCoeffs {t : JasminTy} (k : Nat)
    (kont : HawkMulEmit.Cont t) (f : (Fin M → BitVec 32) → ⟦t⟧)
    (hk : Respects kont f) :
    Respects (coeffsCont k kont) (fun σ => f (coeffsModel k σ)) := by
  intro Γ st V
  show (emitCoeffs k st kont).denote V = f (coeffsModel k (slotMap st V))
  by_cases hkN : k < HawkMulEmit.N
  · have ih := respects_emitCoeffs (k + 1) kont f hk
    have hstep := respects_emitCoeff k (coeffsCont (k + 1) kont) _ ih
    have hE : (emitCoeffs k st kont) =
        emitCoeff k st (fun st1 => emitCoeffs (k + 1) st1 kont) := by
      conv_lhs => rw [HawkMulEmit.emitCoeffs.eq_def]
      simp only [hkN, if_true]
    rw [hE]
    have := hstep Γ st V
    rw [this]
    conv_rhs => rw [coeffsModel.eq_def]
    simp only [hkN, if_true]
  · have hE : (emitCoeffs k st kont) = kont st := by
      conv_lhs => rw [HawkMulEmit.emitCoeffs.eq_def]; simp only [hkN, if_false]
    have hM : coeffsModel k (slotMap st V) = slotMap st V := by
      conv_lhs => rw [coeffsModel.eq_def]; simp only [hkN, if_false]
    rw [hE, hk Γ st V, hM]
termination_by HawkMulEmit.N - k

/-! ## 4. The full kernel denotation as a pure slot-map computation

Chaining the three lifting lemmas: `hawkMulCom`'s denotation is the pure model
`maskModel 0 ∘ coeffsModel 0` applied to the **initial** slot map, read off at
`out[15]` (the returned coefficient). This collapses the 512-binding Jasmin
denotation to a pure `Fin M → BitVec 32` pipeline; the dialect semantics were
used only in `emitOp_slotMap`. -/

/-- **The whole-kernel denotation.** `hawkMulCom.denote V` equals the pure
    slot-map pipeline `maskModel 0 (coeffsModel 0 (slotMap initBState V))` read at
    the returned slot `out[N-1]`. -/
theorem hawkMulCom_denote (V : Ctxt.Valuation HawkMulEmit.inCtxt) :
    HawkMulEmit.hawkMulCom.denote V
      = maskModel 0 (coeffsModel 0 (slotMap HawkMulEmit.initBState V)) (outSlot (HawkMulEmit.N - 1)) := by
  have hret := respects_ret (HawkMulEmit.N - 1)
  have hmask := respects_emitMasks 0 _ _ hret
  have hcoeffs := respects_emitCoeffs 0 (masksCont 0 (fun st => .ret (st.st (outSlot (HawkMulEmit.N - 1))))) _ hmask
  have := hcoeffs HawkMulEmit.inCtxt HawkMulEmit.initBState V
  simpa [HawkMulEmit.hawkMulCom, coeffsCont, masksCont] using this

/-! ## 5. Encoding `HawkLane`s into the input valuation

A pair of lanes `a b : HawkLane = Fin 16 → ZMod 1024` is encoded into the
33-word input valuation: word `i` (`i < 16`) holds `a i`, word `16 + i` holds
`b i`, and word `32` holds the mask constant `1023`. The slot map of `initBState`
under this valuation then has the `a`/`b` coefficients in slots `0..15`/`16..31`
and `1023` in the mask slot `49`. -/

/-- Embed a `ZMod 1024` coefficient as a `BitVec 32` (its canonical `< 1024`
    representative). -/
def embZ (z : Zq1024) : BitVec 32 := BitVec.ofNat 32 z.val

/-- Build a `Valuation (List.replicate n r32)` from a positional word function
    `g : Nat → BitVec 32` (entry `j` of the replicate-context gets `g j`). -/
def mkVal (g : Nat → BitVec 32) :
    (n : Nat) → @Ctxt.Valuation jasminDialect _ (List.replicate n r32)
  | 0 => .nil
  | (n + 1) => .cons (g 0) (mkVal (fun j => g (j + 1)) n)

/-- The positional word function for the encoding of lanes `a, b`:
    `i < 16 ↦ (a i).val`, `16 ≤ i < 32 ↦ (b (i-16)).val`, `i = 32 ↦ 1023`. -/
def encWords (a b : HawkLane) : Nat → BitVec 32 :=
  fun i =>
    if h : i < 16 then embZ (a ⟨i, by simpa [HawkMul4WayEmit.N] using h⟩)
    else if h2 : i < 32 then embZ (b ⟨i - 16, by simp only [HawkMul4WayEmit.N]; omega⟩)
    else BitVec.ofNat 32 1023

/-- The input valuation encoding lanes `a, b` (+ the mask constant `1023`). -/
def encode (a b : HawkLane) : Ctxt.Valuation HawkMulEmit.inCtxt :=
  mkVal (encWords a b) 33

/-- Looking up input word `i ≤ m` in `mkVal g (m+1)` returns `g i`. -/
theorem inputVar_lookup_mkVal (g : Nat → BitVec 32) :
    ∀ (m i : Nat), i ≤ m →
      (HawkMulEmit.inputVar m i).lookup (mkVal g (m + 1)) = g i
  | _, 0, _ => by
      unfold HawkMulEmit.inputVar mkVal Ctxt.Var.lookup; rfl
  | 0, (i + 1), h => by omega
  | (m + 1), (i + 1), h => by
      unfold HawkMulEmit.inputVar mkVal Ctxt.Var.lookup
      exact inputVar_lookup_mkVal (fun j => g (j + 1)) m i (by omega)

/-- The looked-up value of input word `i` (`i < 33`) under `encode a b`. -/
theorem inVar_encode (a b : HawkLane) (i : Nat) (h : i < 33) :
    (HawkMulEmit.inVar i).lookup (encode a b) = encWords a b i := by
  unfold HawkMulEmit.inVar encode
  exact inputVar_lookup_mkVal _ 32 i (by omega)

/-- The **initial slot map** of `initBState` under `encode a b`: slots `0..15`
    hold `a`'s coefficients, slots `16..31` hold `b`'s, the mask slot `49` holds
    `1023`; the `out` slots `32..47` and `scratch` `48` hold the junk seed
    `encWords a b 0` (always overwritten by a `mul` before any read). -/
theorem slotMap_initBState_encode (a b : HawkLane) :
    slotMap HawkMulEmit.initBState (encode a b)
      = fun i =>
          if i.val < 32 then encWords a b i.val
          else if i.val = 49 then BitVec.ofNat 32 1023
          else encWords a b 0 := by
  funext i
  unfold slotMap HawkMulEmit.initBState
  by_cases h1 : i.val < 32
  · simp only [h1, if_true]
    rw [inVar_encode a b i.val (by omega)]
  · simp only [h1, if_false]
    by_cases h2 : i.val = 49
    · simp only [h2, if_true]
      rw [inVar_encode a b 32 (by omega)]
      simp only [encWords]
      norm_num
    · simp only [h2, if_false]
      rw [inVar_encode a b 0 (by omega)]

/-! ## 6. The convolution at the BitVec level

`coeffModel`/`tailModel` accumulate the negacyclic schoolbook product over
`BitVec 32`. We track the running value in `out[k]` as a `BitVec` partial sum and
prove, by the model's own recursion, that `coeffModel k σ (out[k])` equals the
full BitVec convolution. The `& 1023` mask then bridges to `ZMod 1024`. -/

/-- One BitVec convolution term at output `k`, term `i`, over the slot map's `a`
    (slots `0..15`) and `b` (slots `16..31`): the product `a[i]·b[partner k i]`
    with the negacyclic sign (`+` if `i ≤ k`, `−` if `i > k`). -/
def bvTerm (σ : Fin M → BitVec 32) (k i : Nat) : BitVec 32 :=
  if i ≤ k then σ (aSlot i) * σ (bSlot (partner k i))
  else 0 - σ (aSlot i) * σ (bSlot (partner k i))

/-- Running BitVec accumulator in `out[k]` after terms `i … N-1` have been added
    to the start value `acc`: mirrors `tailModel`'s `+`/`−` accumulation. -/
def bvAccum (σ : Fin M → BitVec 32) (k : Nat) : Nat → BitVec 32 → BitVec 32
  | i, acc =>
    if i < HawkMulEmit.N then bvAccum σ k (i + 1) (acc + bvTerm σ k i)
    else acc
  termination_by i => HawkMulEmit.N - i

/-! ### Slot disjointness

`a`-slots (`0..15`) and `b`-slots (`16..31`) are disjoint from any `out`-slot
(`32..47`) and from `scratch` (`48`), so the accumulation updates never disturb
the inputs the products read. -/

theorem aSlot_ne_outSlot (i k : Nat) : aSlot i ≠ outSlot k := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.aSlot, HawkMulEmit.outSlot, HawkMulEmit.N] at this; omega

theorem aSlot_ne_scrSlot (i : Nat) : aSlot i ≠ scrSlot := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.aSlot, HawkMulEmit.scrSlot, HawkMulEmit.N] at this; omega

theorem bSlot_ne_outSlot (j k : Nat) : bSlot j ≠ outSlot k := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.bSlot, HawkMulEmit.outSlot, HawkMulEmit.N] at this; omega

theorem bSlot_ne_scrSlot (j : Nat) : bSlot j ≠ scrSlot := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.bSlot, HawkMulEmit.scrSlot, HawkMulEmit.N] at this; omega

theorem scrSlot_ne_outSlot (k : Nat) : scrSlot ≠ outSlot k := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.scrSlot, HawkMulEmit.outSlot, HawkMulEmit.N] at this; omega

/-- `bvAccum` depends on the slot map only through the `a`/`b` slots: if `σ` and
    `σ'` agree on every `aSlot`/`bSlot`, they give the same accumulator. -/
theorem bvAccum_congr (σ σ' : Fin M → BitVec 32) (k : Nat)
    (ha : ∀ m, σ (aSlot m) = σ' (aSlot m)) (hb : ∀ m, σ (bSlot m) = σ' (bSlot m)) :
    ∀ (i : Nat) (acc : BitVec 32), bvAccum σ k i acc = bvAccum σ' k i acc
  | i, acc => by
    by_cases hiN : i < HawkMulEmit.N
    · have ih := bvAccum_congr σ σ' k ha hb (i + 1)
      have hterm : bvTerm σ k i = bvTerm σ' k i := by
        unfold bvTerm; rw [ha, hb]
      conv_lhs => rw [bvAccum.eq_def]
      conv_rhs => rw [bvAccum.eq_def]
      simp only [hiN, if_true, hterm]
      rw [ih]
    · conv_lhs => rw [bvAccum.eq_def]
      conv_rhs => rw [bvAccum.eq_def]
      simp only [hiN, if_false]
termination_by i => HawkMulEmit.N - i

/-- `tailModel` accumulates `out[k]` exactly as `bvAccum` does, leaving the
    `a`/`b` slots untouched (so each term reads the original inputs). -/
theorem tailModel_outSlot (σ : Fin M → BitVec 32) (k i : Nat) :
    tailModel k i σ (outSlot k) = bvAccum σ k i (σ (outSlot k)) := by
  by_cases hiN : i < HawkMulEmit.N
  · set P : BitVec 32 := JasminBinOp.apply .mul (σ (aSlot i)) (σ (bSlot (partner k i))) with hP
    set σ1 := Function.update σ scrSlot P with hσ1
    set σ2 := Function.update σ1 (outSlot k)
      (JasminBinOp.apply (if i ≤ k then .add else .sub) (σ1 (outSlot k)) (σ1 scrSlot)) with hσ2
    have ih := tailModel_outSlot σ2 k (i + 1)
    rw [tailModel.eq_def]
    simp only [hiN, if_true]
    change tailModel k (i + 1) σ2 (outSlot k) = _
    rw [ih]
    -- σ2 agrees with σ on a/b slots
    have haσ2 : ∀ m, σ2 (aSlot m) = σ (aSlot m) := by
      intro m; rw [hσ2, hσ1]
      rw [Function.update_of_ne (aSlot_ne_outSlot m k),
          Function.update_of_ne (aSlot_ne_scrSlot m)]
    have hbσ2 : ∀ m, σ2 (bSlot m) = σ (bSlot m) := by
      intro m; rw [hσ2, hσ1]
      rw [Function.update_of_ne (bSlot_ne_outSlot m k),
          Function.update_of_ne (bSlot_ne_scrSlot m)]
    rw [bvAccum_congr σ2 σ k haσ2 hbσ2]
    -- σ2 (outSlot k) = σ (outSlot k) + bvTerm σ k i; and bvAccum's first step.
    have hσ1out : σ1 (outSlot k) = σ (outSlot k) := by
      rw [hσ1, Function.update_of_ne (scrSlot_ne_outSlot k).symm]
    have hσ1scr : σ1 scrSlot = P := by rw [hσ1, Function.update_self]
    have hσ2out : σ2 (outSlot k) = σ (outSlot k) + bvTerm σ k i := by
      rw [hσ2, Function.update_self, hσ1out, hσ1scr, hP]
      unfold bvTerm JasminBinOp.apply
      by_cases hik : i ≤ k <;> simp only [hik, if_true, if_false]
      rw [sub_eq_add_neg]
      rw [zero_sub]
    rw [hσ2out]
    -- bvAccum σ k i (σ outSlot) steps to bvAccum σ k (i+1) (σ outSlot + bvTerm)
    conv_rhs => rw [bvAccum.eq_def]
    simp only [hiN, if_true]
  · rw [tailModel.eq_def, bvAccum.eq_def]
    simp only [hiN, if_false]
termination_by HawkMulEmit.N - i

/-- **`coeffModel` computes the full BitVec convolution into `out[k]`.** The
    first product seeds `out[k]` with `bvTerm σ k 0` and the tail adds terms
    `1 … N-1`; together that is `bvAccum σ k 0 0`, the whole negacyclic sum. -/
theorem coeffModel_outSlot (σ : Fin M → BitVec 32) (k : Nat) :
    coeffModel k σ (outSlot k) = bvAccum σ k 0 0 := by
  unfold coeffModel
  set σ0 := Function.update σ (outSlot k)
    (JasminBinOp.apply .mul (σ (aSlot 0)) (σ (bSlot (partner k 0)))) with hσ0
  rw [tailModel_outSlot σ0 k 1]
  -- σ0 agrees with σ on a/b slots
  have haσ0 : ∀ m, σ0 (aSlot m) = σ (aSlot m) := fun m => by
    rw [hσ0, Function.update_of_ne (aSlot_ne_outSlot m k)]
  have hbσ0 : ∀ m, σ0 (bSlot m) = σ (bSlot m) := fun m => by
    rw [hσ0, Function.update_of_ne (bSlot_ne_outSlot m k)]
  rw [bvAccum_congr σ0 σ k haσ0 hbσ0]
  have hσ0out : σ0 (outSlot k) = bvTerm σ k 0 := by
    rw [hσ0, Function.update_self]
    unfold bvTerm JasminBinOp.apply
    simp only [Nat.zero_le, if_true]
  rw [hσ0out]
  -- bvAccum σ k 0 0 = bvAccum σ k 1 (0 + bvTerm σ k 0) = bvAccum σ k 1 (bvTerm σ k 0)
  conv_rhs => rw [bvAccum.eq_def]
  simp only [show (0 : Nat) < HawkMulEmit.N by decide, if_true, zero_add]

/-! ### `coeffsModel` reads each `out[k]` off the original inputs

`coeffModel`/`tailModel` write only `out`- and `scratch`-slots, so they preserve
all `a`/`b` slots; and `coeffModel k'` for `k' ≠ k` leaves `out[k]` untouched
(`outSlot` is injective on `0..N-1`). Hence within `coeffsModel 0`, the slot
`out[k]` ends up holding `coeffModel k`'s output computed from the *original*
`a`/`b`, i.e. `bvAccum σ k 0 0`. -/

/-- `tailModel` preserves `a`-slots (writes only `out[k]`/`scratch`). -/
theorem tailModel_aSlot (σ : Fin M → BitVec 32) (k m : Nat) (i : Nat) :
    tailModel k i σ (aSlot m) = σ (aSlot m) := by
  rw [tailModel.eq_def]
  by_cases hiN : i < HawkMulEmit.N
  · simp only [hiN, if_true]
    rw [tailModel_aSlot _ k m (i + 1),
        Function.update_of_ne (aSlot_ne_outSlot m k),
        Function.update_of_ne (aSlot_ne_scrSlot m)]
  · simp only [hiN, if_false]
  termination_by HawkMulEmit.N - i

/-- `tailModel` preserves `b`-slots. -/
theorem tailModel_bSlot (σ : Fin M → BitVec 32) (k m : Nat) (i : Nat) :
    tailModel k i σ (bSlot m) = σ (bSlot m) := by
  rw [tailModel.eq_def]
  by_cases hiN : i < HawkMulEmit.N
  · simp only [hiN, if_true]
    rw [tailModel_bSlot _ k m (i + 1),
        Function.update_of_ne (bSlot_ne_outSlot m k),
        Function.update_of_ne (bSlot_ne_scrSlot m)]
  · simp only [hiN, if_false]
  termination_by HawkMulEmit.N - i

/-- `tailModel k` preserves `out[k']` for `k' ≠ k` (mod N). -/
theorem tailModel_outSlot_ne (σ : Fin M → BitVec 32) (k k' : Nat)
    (hne : outSlot k' ≠ outSlot k) (i : Nat) :
    tailModel k i σ (outSlot k') = σ (outSlot k') := by
  rw [tailModel.eq_def]
  by_cases hiN : i < HawkMulEmit.N
  · simp only [hiN, if_true]
    rw [tailModel_outSlot_ne _ k k' hne (i + 1),
        Function.update_of_ne hne, Function.update_of_ne (scrSlot_ne_outSlot k').symm]
  · simp only [hiN, if_false]
  termination_by HawkMulEmit.N - i

theorem coeffModel_aSlot (σ : Fin M → BitVec 32) (k m : Nat) :
    coeffModel k σ (aSlot m) = σ (aSlot m) := by
  unfold coeffModel
  rw [tailModel_aSlot, Function.update_of_ne (aSlot_ne_outSlot m k)]

theorem coeffModel_bSlot (σ : Fin M → BitVec 32) (k m : Nat) :
    coeffModel k σ (bSlot m) = σ (bSlot m) := by
  unfold coeffModel
  rw [tailModel_bSlot, Function.update_of_ne (bSlot_ne_outSlot m k)]

/-- `coeffModel k` preserves `out[k']` for `k' ≠ k` (mod N). -/
theorem coeffModel_outSlot_ne (σ : Fin M → BitVec 32) (k k' : Nat)
    (hne : outSlot k' ≠ outSlot k) :
    coeffModel k σ (outSlot k') = σ (outSlot k') := by
  unfold coeffModel
  rw [tailModel_outSlot_ne _ k k' hne, Function.update_of_ne hne]

/-- `outSlot` is injective on `0 … N-1` (`k % N = k` there). -/
theorem outSlot_inj (k k' : Nat) (hk : k < HawkMulEmit.N) (hk' : k' < HawkMulEmit.N)
    (h : outSlot k = outSlot k') : k = k' := by
  have hv := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.outSlot, HawkMulEmit.N] at hv hk hk'
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at hv
  omega

/-- `coeffsModel` preserves `a`-slots. -/
theorem coeffsModel_aSlot (σ : Fin M → BitVec 32) (m : Nat) (k : Nat) :
    coeffsModel k σ (aSlot m) = σ (aSlot m) := by
  rw [coeffsModel.eq_def]
  by_cases hkN : k < HawkMulEmit.N
  · simp only [hkN, if_true]
    rw [coeffsModel_aSlot _ m (k + 1), coeffModel_aSlot]
  · simp only [hkN, if_false]
  termination_by HawkMulEmit.N - k

/-- `coeffsModel` preserves `b`-slots. -/
theorem coeffsModel_bSlot (σ : Fin M → BitVec 32) (m : Nat) (k : Nat) :
    coeffsModel k σ (bSlot m) = σ (bSlot m) := by
  rw [coeffsModel.eq_def]
  by_cases hkN : k < HawkMulEmit.N
  · simp only [hkN, if_true]
    rw [coeffsModel_bSlot _ m (k + 1), coeffModel_bSlot]
  · simp only [hkN, if_false]
  termination_by HawkMulEmit.N - k

/-- After `coeffModel j` has set `out[j]`, the later coeffs `coeffsModel start …`
    (`start > k`) leave `out[k]` untouched (they write `out[j']` for `j' > k`,
    distinct mod `N`), so its value is preserved. -/
theorem coeffsModel_outSlot_preserved (σ : Fin M → BitVec 32) (start k : Nat)
    (hstart : k < start) (hkN : k < HawkMulEmit.N) :
    coeffsModel start σ (outSlot k) = σ (outSlot k) := by
  rw [coeffsModel.eq_def]
  by_cases hsN : start < HawkMulEmit.N
  · simp only [hsN, if_true]
    have hne : outSlot k ≠ outSlot start := by
      intro h; exact absurd (outSlot_inj k start hkN hsN h) (by omega)
    rw [coeffsModel_outSlot_preserved (coeffModel start σ) (start + 1) k (by omega) hkN]
    rw [coeffModel_outSlot_ne σ start k hne]
  · simp only [hsN, if_false]
  termination_by HawkMulEmit.N - start

/-- **`coeffsModel j` writes the full convolution into each `out[k]`** for
    `j ≤ k < N`: the slot is set by `coeffModel k` (reading the still-original
    `a`/`b`) and untouched by every other `coeffModel`. So
    `coeffsModel j σ (out[k]) = bvAccum σ k 0 0`. -/
theorem coeffsModel_outSlot (σ : Fin M → BitVec 32) (j k : Nat)
    (hjk : j ≤ k) (hkN : k < HawkMulEmit.N) :
    coeffsModel j σ (outSlot k) = bvAccum σ k 0 0 := by
  rw [coeffsModel.eq_def]
  have hjN : j < HawkMulEmit.N := lt_of_le_of_lt hjk hkN
  simp only [hjN, if_true]
  rcases Nat.lt_or_ge j k with hlt | hge
  · -- j < k: coeffModel j leaves out[k] alone; recurse, but a/b preserved
    have ih := coeffsModel_outSlot (coeffModel j σ) (j + 1) k (by omega) hkN
    rw [ih]
    -- bvAccum over coeffModel j σ = bvAccum over σ (a/b preserved by coeffModel j)
    rw [bvAccum_congr (coeffModel j σ) σ k
      (fun m => coeffModel_aSlot σ j m) (fun m => coeffModel_bSlot σ j m)]
  · -- j = k
    have hjeqk : j = k := le_antisymm hjk hge
    subst hjeqk
    rw [coeffsModel_outSlot_preserved (coeffModel j σ) (j + 1) j (by omega) hjN]
    rw [coeffModel_outSlot σ j]
termination_by HawkMulEmit.N - j

theorem maskConstSlot_ne_outSlot (k : Nat) : maskConstSlot ≠ outSlot k := by
  intro h; have := Fin.val_eq_of_eq h
  simp only [HawkMulEmit.maskConstSlot, HawkMulEmit.outSlot, HawkMulEmit.N] at this; omega

/-- `tailModel`/`coeffModel`/`coeffsModel` preserve the mask-constant slot
    (they write only `out`/`scratch`). -/
theorem tailModel_maskConstSlot (σ : Fin M → BitVec 32) (k i : Nat) :
    tailModel k i σ maskConstSlot = σ maskConstSlot := by
  rw [tailModel.eq_def]
  by_cases hiN : i < HawkMulEmit.N
  · simp only [hiN, if_true]
    rw [tailModel_maskConstSlot _ k (i + 1),
        Function.update_of_ne (maskConstSlot_ne_outSlot k),
        Function.update_of_ne (by
          intro h; have := Fin.val_eq_of_eq h
          simp only [HawkMulEmit.maskConstSlot, HawkMulEmit.scrSlot] at this; omega)]
  · simp only [hiN, if_false]
  termination_by HawkMulEmit.N - i

theorem coeffModel_maskConstSlot (σ : Fin M → BitVec 32) (k : Nat) :
    coeffModel k σ maskConstSlot = σ maskConstSlot := by
  unfold coeffModel
  rw [tailModel_maskConstSlot, Function.update_of_ne (maskConstSlot_ne_outSlot k)]

theorem coeffsModel_maskConstSlot (σ : Fin M → BitVec 32) (k : Nat) :
    coeffsModel k σ maskConstSlot = σ maskConstSlot := by
  rw [coeffsModel.eq_def]
  by_cases hkN : k < HawkMulEmit.N
  · simp only [hkN, if_true]
    rw [coeffsModel_maskConstSlot _ (k + 1), coeffModel_maskConstSlot]
  · simp only [hkN, if_false]
  termination_by HawkMulEmit.N - k

/-! ### `maskModel` applies the `& 1023` reduction to each `out[k]` -/

/-- `maskModel` preserves the mask-constant slot. -/
theorem maskModel_maskConstSlot (σ : Fin M → BitVec 32) (j : Nat) :
    maskModel j σ maskConstSlot = σ maskConstSlot := by
  rw [maskModel.eq_def]
  by_cases hjN : j < HawkMulEmit.N
  · simp only [hjN, if_true]
    rw [maskModel_maskConstSlot _ (j + 1),
        Function.update_of_ne (maskConstSlot_ne_outSlot j)]
  · simp only [hjN, if_false]
  termination_by HawkMulEmit.N - j

/-- `maskModel start` (`start > k`) leaves `out[k]` untouched. -/
theorem maskModel_outSlot_preserved (σ : Fin M → BitVec 32) (start k : Nat)
    (hstart : k < start) (hkN : k < HawkMulEmit.N) :
    maskModel start σ (outSlot k) = σ (outSlot k) := by
  rw [maskModel.eq_def]
  by_cases hsN : start < HawkMulEmit.N
  · simp only [hsN, if_true]
    have hne : outSlot k ≠ outSlot start := by
      intro h; exact absurd (outSlot_inj k start hkN hsN h) (by omega)
    rw [maskModel_outSlot_preserved _ (start + 1) k (by omega) hkN,
        Function.update_of_ne hne]
  · simp only [hsN, if_false]
  termination_by HawkMulEmit.N - start

/-- **`maskModel j` masks each `out[k]`** (`j ≤ k < N`): the value at `out[k]`
    becomes `out[k] & maskConst`, where `maskConst` is the (preserved) mask slot.
    `maskModel j σ (out[k]) = σ (out[k]) &&& σ maskConstSlot`. -/
theorem maskModel_outSlot (σ : Fin M → BitVec 32) (j k : Nat)
    (hjk : j ≤ k) (hkN : k < HawkMulEmit.N) :
    maskModel j σ (outSlot k) = σ (outSlot k) &&& σ maskConstSlot := by
  rw [maskModel.eq_def]
  have hjN : j < HawkMulEmit.N := lt_of_le_of_lt hjk hkN
  simp only [hjN, if_true]
  rcases Nat.lt_or_ge j k with hlt | hge
  · have hne : outSlot k ≠ outSlot j := by
      intro h; exact absurd (outSlot_inj k j hkN hjN h) (by omega)
    rw [maskModel_outSlot (Function.update σ (outSlot j) _) (j + 1) k (by omega) hkN]
    rw [Function.update_of_ne hne, Function.update_of_ne (maskConstSlot_ne_outSlot j)]
  · have hjeqk : j = k := le_antisymm hjk hge
    subst hjeqk
    rw [maskModel_outSlot_preserved _ (j + 1) j (by omega) hjN]
    rw [Function.update_self]
    rfl
termination_by HawkMulEmit.N - j

/-! ## 7. The full slot-level convolution tie

Combining §4–§6: under the encoded input, the final slot map holds, at each
`out[k]`, the BitVec negacyclic convolution masked by `& 1023`. -/

/-- **Per-coefficient BitVec result.** For every output coefficient `k < N`, the
    final slot map (`maskModel 0 ∘ coeffsModel 0` of the initial map) holds
    `bvAccum σ k 0 0 &&& 1023` at `out[k]` — the BitVec negacyclic convolution,
    reduced mod `1024`. -/
theorem final_outSlot (a b : HawkLane) (k : Nat) (hk : k < HawkMulEmit.N) :
    maskModel 0 (coeffsModel 0 (slotMap HawkMulEmit.initBState (encode a b))) (outSlot k)
      = (bvAccum (slotMap HawkMulEmit.initBState (encode a b)) k 0 0) &&& BitVec.ofNat 32 1023 := by
  set σ0 := slotMap HawkMulEmit.initBState (encode a b) with hσ0
  rw [maskModel_outSlot (coeffsModel 0 σ0) 0 k (by omega) hk]
  rw [coeffsModel_outSlot σ0 0 k (by omega) hk]
  rw [coeffsModel_maskConstSlot σ0 0]
  -- the mask slot of the initial map is 1023
  rw [show σ0 maskConstSlot = BitVec.ofNat 32 1023 from by
    rw [hσ0, slotMap_initBState_encode]; norm_num [HawkMulEmit.maskConstSlot]]

/-! ## 8. The BitVec → `ZMod 1024` bridge

`φ x = (x.toNat : ZMod 1024)` is a ring map (because `1024 ∣ 2^32`, reducing mod
`2^32` first is invisible mod `1024`). It sends `embZ z ↦ z`, is invariant under
`& 1023` (the field mask), and turns the BitVec convolution into the `ZMod`
`Finset.sum`. Since both `bvAccum … &&& 1023` and `embZ spec` are `< 1024`,
equality of their `φ`-images upgrades to BitVec equality. -/

/-- The reduction map `BitVec 32 → ZMod 1024`. -/
def φ (x : BitVec 32) : Zq1024 := (x.toNat : ZMod 1024)

theorem φ_dvd (n : Nat) : ((n % 4294967296 : Nat) : ZMod 1024) = (n : ZMod 1024) := by
  rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_mod_of_dvd n (by norm_num)

theorem φ_add (a b : BitVec 32) : φ (a + b) = φ a + φ b := by
  unfold φ; rw [BitVec.toNat_add, φ_dvd]; push_cast; ring

theorem φ_mul (a b : BitVec 32) : φ (a * b) = φ a * φ b := by
  unfold φ; rw [BitVec.toNat_mul, φ_dvd]; push_cast; ring

theorem φ_sub (a b : BitVec 32) : φ (a - b) = φ a - φ b := by
  unfold φ
  rw [BitVec.toNat_sub, φ_dvd]
  have hble : b.toNat ≤ 2 ^ 32 := le_of_lt (by have := b.isLt; omega)
  rw [Nat.cast_add, Nat.cast_sub hble]
  rw [show ((2 ^ 32 : ℕ) : ZMod 1024) = 0 from by
    rw [show (2 ^ 32 : ℕ) = 1024 * 2 ^ 22 from by norm_num, Nat.cast_mul,
      ZMod.natCast_self]; ring]
  ring

theorem φ_embZ (z : Zq1024) : φ (embZ z) = z := by
  unfold φ embZ
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := z.val_lt (n := 1024); omega)]
  exact ZMod.natCast_zmod_val z

theorem φ_zero : φ 0 = 0 := by unfold φ; simp

/-- The field mask `& 1023` is `mod 1024` at the `Nat` level. -/
theorem mask_toNat (x : BitVec 32) : (x &&& BitVec.ofNat 32 1023).toNat = x.toNat % 1024 := by
  rw [BitVec.toNat_and]; simp only [BitVec.toNat_ofNat]
  rw [Nat.and_two_pow_sub_one_eq_mod (n := 10)]

/-- `φ` is invariant under the field mask: masking is invisible mod `1024`. -/
theorem φ_mask (x : BitVec 32) : φ (x &&& BitVec.ofNat 32 1023) = φ x := by
  unfold φ; rw [mask_toNat]
  rw [ZMod.natCast_eq_natCast_iff']; exact Nat.mod_mod_of_dvd x.toNat (by norm_num)

/-- The masked value is `< 1024`, so it is its own canonical `ZMod 1024`
    representative: `embZ (φ (x & 1023)) = x & 1023`. -/
theorem embZ_φ_mask (x : BitVec 32) :
    embZ (φ (x &&& BitVec.ofNat 32 1023)) = x &&& BitVec.ofNat 32 1023 := by
  apply BitVec.eq_of_toNat_eq
  unfold embZ φ
  rw [BitVec.toNat_ofNat]
  have hlt : (x &&& BitVec.ofNat 32 1023).toNat < 1024 := by
    rw [mask_toNat]; exact Nat.mod_lt _ (by norm_num)
  rw [ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## 9. The convolution bridge: `φ (bvAccum) = hawkNegacyclicMul`

`φ` carries the BitVec running accumulator to the `ZMod 1024` partial sum, and
each `bvTerm` of the encoded input to the spec's `negaTerm`. So the full BitVec
convolution reduces to `hawkNegacyclicMul`. -/

open scoped BigOperators

/-- `φ` turns the BitVec accumulator into the `ZMod` partial sum over `[i, N)`. -/
theorem φ_bvAccum (σ : Fin M → BitVec 32) (k : Nat) (i : Nat) (acc : BitVec 32) :
    φ (bvAccum σ k i acc) = φ acc + ∑ j ∈ Finset.Ico i HawkMulEmit.N, φ (bvTerm σ k j) := by
  rw [bvAccum.eq_def]
  by_cases hiN : i < HawkMulEmit.N
  · simp only [hiN, if_true]
    rw [φ_bvAccum σ k (i + 1) (acc + bvTerm σ k i)]
    rw [φ_add]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show HawkMulEmit.N - i = (HawkMulEmit.N - (i + 1)) + 1 from by omega]
    rw [Finset.sum_range_succ']
    simp only [add_zero]
    have hSeq : (∑ k_1 ∈ Finset.range (HawkMulEmit.N - (i + 1)), φ (bvTerm σ k (i + 1 + k_1)))
        = ∑ k_1 ∈ Finset.range (HawkMulEmit.N - (i + 1)), φ (bvTerm σ k (i + (k_1 + 1))) := by
      apply Finset.sum_congr rfl; intro x _
      rw [show i + 1 + x = i + (x + 1) from by omega]
    rw [hSeq]; ring
  · simp only [hiN, if_false]
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  termination_by HawkMulEmit.N - i

/-- The initial slot map's `a`-slot `i` holds `embZ (a ⟨i % N⟩)`. -/
theorem initσ_aSlot (a b : HawkLane) (i : Nat) :
    slotMap HawkMulEmit.initBState (encode a b) (aSlot i)
      = embZ (a ⟨i % HawkMulEmit.N, Nat.mod_lt _ (by decide)⟩) := by
  rw [slotMap_initBState_encode]
  have haval : (aSlot i).val = i % HawkMulEmit.N := by simp only [HawkMulEmit.aSlot]
  have hlt16 : (aSlot i).val < 16 := by
    rw [haval]; have : i % HawkMulEmit.N < HawkMulEmit.N := Nat.mod_lt _ (by decide)
    simp only [HawkMulEmit.N] at *; omega
  have hlt : (aSlot i).val < 32 := by omega
  simp only [hlt, if_true, encWords, dif_pos hlt16]
  congr 1

/-- The initial slot map's `b`-slot `j` holds `embZ (b ⟨j % N⟩)`. -/
theorem initσ_bSlot (a b : HawkLane) (j : Nat) :
    slotMap HawkMulEmit.initBState (encode a b) (bSlot j)
      = embZ (b ⟨j % HawkMulEmit.N, Nat.mod_lt _ (by decide)⟩) := by
  rw [slotMap_initBState_encode]
  have hbval : (bSlot j).val = 16 + j % HawkMulEmit.N := by
    simp only [HawkMulEmit.bSlot, HawkMulEmit.N]
  have hlt : (bSlot j).val < 32 := by
    rw [hbval]; have : j % HawkMulEmit.N < HawkMulEmit.N := Nat.mod_lt _ (by decide)
    simp only [HawkMulEmit.N] at *; omega
  have hnlt16 : ¬ (bSlot j).val < 16 := by rw [hbval]; omega
  simp only [hlt, if_true, encWords, dif_neg hnlt16, dite_true]
  have hval : (bSlot j).val - 16 = j % HawkMulEmit.N := by
    rw [hbval]; simp only [HawkMulEmit.N]; omega
  congr 2
  apply Fin.ext
  exact hval

/-- For `i, k < N`, `φ` of the BitVec convolution term equals the spec's
    `negaTerm` of the encoded lanes. -/
theorem φ_bvTerm (a b : HawkLane) (k i : Nat) (hk : k < HawkMulEmit.N)
    (hi : i < HawkMulEmit.N) :
    φ (bvTerm (slotMap HawkMulEmit.initBState (encode a b)) k i)
      = negaTerm a b ⟨k, hk⟩ ⟨i, hi⟩ := by
  have ha : φ (slotMap HawkMulEmit.initBState (encode a b) (aSlot i)) = a ⟨i, hi⟩ := by
    rw [initσ_aSlot, φ_embZ]; congr 1; apply Fin.ext
    simp only []; exact Nat.mod_eq_of_lt hi
  have hb : φ (slotMap HawkMulEmit.initBState (encode a b) (bSlot (partner k i)))
      = b ⟨(k + HawkMulEmit.N - i) % HawkMulEmit.N, Nat.mod_lt _ (by decide)⟩ := by
    rw [initσ_bSlot, φ_embZ]; congr 1; apply Fin.ext
    simp only [HawkMulEmit.partner]
    rw [Nat.mod_mod_of_dvd _ (dvd_refl _)]
  unfold bvTerm negaTerm
  by_cases hik : i ≤ k
  · simp only [hik, if_true]
    rw [φ_mul, ha, hb]
  · simp only [hik, if_false]
    rw [zero_sub]
    rw [show φ (-(slotMap HawkMulEmit.initBState (encode a b) (aSlot i)
          * slotMap HawkMulEmit.initBState (encode a b) (bSlot (partner k i))))
        = -(φ (slotMap HawkMulEmit.initBState (encode a b) (aSlot i)
          * slotMap HawkMulEmit.initBState (encode a b) (bSlot (partner k i)))) from by
      rw [← zero_sub, φ_sub, φ_zero, zero_sub]]
    rw [φ_mul, ha, hb]

/-- The full BitVec convolution at coefficient `k`, reduced by `φ`, is exactly
    the spec `hawkNegacyclicMul a b ⟨k⟩` (a `Finset.sum` of `negaTerm`s). -/
theorem φ_bvAccum_eq_spec (a b : HawkLane) (k : Nat) (hk : k < HawkMulEmit.N) :
    φ (bvAccum (slotMap HawkMulEmit.initBState (encode a b)) k 0 0)
      = hawkNegacyclicMul a b ⟨k, hk⟩ := by
  rw [φ_bvAccum, φ_zero, zero_add]
  unfold hawkNegacyclicMul
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.zero_add, Nat.sub_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun j => φ (bvTerm (slotMap HawkMulEmit.initBState (encode a b)) k j))]
  apply Finset.sum_congr rfl
  intro x _
  rw [φ_bvTerm a b k x.val hk x.isLt]

/-! ## 10. The HAWK Com-denotation ⟷ spec tie (full N=16)

This is the headline result: the emitted `Com jasminDialect` kernel `hawkMulCom`,
**denoted**, computes the negacyclic product `hawkNegacyclicMul`. -/

/-- **Per-coefficient Com-denotation tie.** The final slot map of `hawkMulCom`'s
    denotation holds, at every output `out[k]` (`k < N = 16`), the embedded
    negacyclic product `embZ (hawkNegacyclicMul a b ⟨k⟩)`. -/
theorem final_outSlot_spec (a b : HawkLane) (k : Nat) (hk : k < HawkMulEmit.N) :
    maskModel 0 (coeffsModel 0 (slotMap HawkMulEmit.initBState (encode a b))) (outSlot k)
      = embZ (hawkNegacyclicMul a b ⟨k, hk⟩) := by
  rw [final_outSlot a b k hk]
  rw [← φ_bvAccum_eq_spec a b k hk]
  rw [← φ_mask (bvAccum (slotMap HawkMulEmit.initBState (encode a b)) k 0 0)]
  rw [embZ_φ_mask]

/-- **The HAWK Com-denotation ⟷ spec tie (FULL `N = 16`).** Denoting the emitted
    `Com jasminDialect` negacyclic-multiply kernel on the encoded lane pair `(a,
    b)` yields exactly the embedded negacyclic product
    `hawkNegacyclicMul a b` at the returned coefficient `out[N-1]`. Because the
    per-coefficient result `final_outSlot_spec` holds for **every** `k < N`, this
    is a full `N = 16` tie of the kernel's denotation to the spec
    `hawkNegacyclicMul` (§HawkMul4WayRealization), bridged through the `& 1023`
    field reduction (`φ_mask`) — not a single-coefficient or degenerate
    instance.

    **Boundary (read `Scope`).** This ties the Com-IR denotation to the abstract
    spec. It is **not** a proof about the emitted x86 `.s` bytes: that depends on
    the Com→jasmin→x86 lowering being denotation-complete downstream, which is
    not established here. The byte identity vs the PQClean-style reference stays
    KAT-anchored. -/
theorem hawkMulCom_denote_spec (a b : HawkLane) :
    HawkMulEmit.hawkMulCom.denote (encode a b)
      = embZ (hawkNegacyclicMul a b ⟨HawkMulEmit.N - 1, by decide⟩) := by
  rw [hawkMulCom_denote]
  rw [final_outSlot_spec a b (HawkMulEmit.N - 1) (by decide)]

end CatCrypt.Crypto.SecureCompilation.VIR.HawkMulComDenoteTie
