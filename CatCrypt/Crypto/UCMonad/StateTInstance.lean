/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.UCMonad

/-!
# StateT Preserves UCMonadMetric

This file proves that the state transformer `StateT S T` preserves the
`UCMonadBase` and `UCMonadMetric` structure, when the base monad `T` already
has them.

## Key insight: uncurrying

The Kleisli category of `StateT S T` is isomorphic to the **Para construction**
(Capucci–Gavranović 2022) applied to `Kl(T)`:

  `Kl(StateT S T)(α, β) ≅ Kl(T)(α × S, β × S)`

A morphism `f : α → StateT S T β = α → S → T (β × S)` is the same as
`Function.uncurry f : α × S → T (β × S)`, a `Kl(T)` morphism between
state-annotated types.

This identification is the foundation of the entire file: **all proofs reduce
to `T`'s axioms via uncurrying**.

## Statistical distance

We define `ucSdist` for `StateT S T` by delegating to `T`:

  `ucSdist_stateT(f, g) = T.ucSdist(uncurry f, uncurry g)`

This treats `(input, initial_state)` as a single compound input to `T`.
Both PPL axioms follow from `T`'s PPLs via the identity:

  `uncurry(f >=>_{StateT} g) = uncurry(f) >=>_T uncurry(g)`

## Compatibility with SPComp

When `S = Heap` and `T = SDistr`, the `StateT Heap SDistr` type is definitionally
`Heap → SDistr (α × Heap) = SPComp α`. Our `ucSdist_stateT` recovers SPComp's
`sdist` (up to the equivalence between stateful and product-domain distinguishers).

## Para/coPara Interpretation

`ProtBicat(StateT S T) = coPara(Para_S(Kl(T)))`:
- 1-cells: `{ iface : Type; prot : (hon × S) → T((out ⊕ iface) × S) }`
- 2-cells: stateful simulators `(P.iface × S) → T(Q.iface × S)`

This gives a formal framework for secure compilation of stateful protocols,
where the generic `UCEmulates ↔ RHP` instantiates to guarantee robust
hyperproperty preservation with stateful contexts and distinguishers.

## References

* Capucci, Gavranović — *Actegories for the Working Amthematician* (2022)
* Bonchi, Milius, Pous, Pratt — *Lawvere Metric Spaces* (BMPP 2022)
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: The Key Identity — Uncurrying StateT Bind

    The central lemma: `uncurry(f >=>_{StateT} g) = uncurry(f) >=>_T uncurry(g)`.
    This is what makes all PPL proofs trivial. -/

section UncurryBind

variable {S : Type} {T : Type → Type} [Monad T]

/-- Uncurried StateT pure = T pure on the product. -/
theorem uncurry_stateT_pure {α : Type} :
    Function.uncurry (pure : α → StateT S T α) =
    (fun (p : α × S) => (pure (p.1, p.2) : T (α × S))) := by
  funext ⟨a, s⟩; rfl

/-- **The key identity**: uncurrying commutes with Kleisli composition.

    `uncurry(f >=>_{StateT S T} g) = uncurry(f) >=>_T uncurry(g)`

    This is the morphism-level statement of the isomorphism
    `Kl(StateT S T) ≅ Para_S(Kl(T))`. -/
theorem uncurry_stateT_bind {α β γ : Type}
    (f : α → StateT S T β) (g : β → StateT S T γ) :
    Function.uncurry (fun a => f a >>= g) =
    (fun p => Function.uncurry f p >>= Function.uncurry g) := by
  funext ⟨a, s⟩; rfl

end UncurryBind

/-! ## Section 2: UCMonadBase for StateT -/

section StateT_UCMonadBase

variable {S : Type} {T : Type → Type} [UCMonadBase T]

/-- Parallel composition on `Sum` for `StateT S T`.

    Defined using StateT-level `>>=` and `pure` so that the inl/inr
    lemmas hold by `rfl`. -/
noncomputable def stateT_ucMapSum {α β γ δ : Type}
    (f : α → StateT S T β) (g : γ → StateT S T δ) :
    (α ⊕ γ) → StateT S T (β ⊕ δ)
  | .inl a => f a >>= fun b => pure (Sum.inl b)
  | .inr c => g c >>= fun d => pure (Sum.inr d)

theorem stateT_ucMapSum_inl {α β γ δ : Type}
    (f : α → StateT S T β) (g : γ → StateT S T δ) (a : α) :
    stateT_ucMapSum f g (.inl a) =
    (f a >>= fun b => (pure (Sum.inl b) : StateT S T (β ⊕ δ))) := rfl

theorem stateT_ucMapSum_inr {α β γ δ : Type}
    (f : α → StateT S T β) (g : γ → StateT S T δ) (c : γ) :
    stateT_ucMapSum f g (.inr c) =
    (g c >>= fun d => (pure (Sum.inr d) : StateT S T (β ⊕ δ))) := rfl

theorem stateT_ucMapSum_pure_pure {α β : Type} :
    stateT_ucMapSum (S := S) (T := T)
      (pure : α → StateT S T α) (pure : β → StateT S T β) = pure := by
  ext x s
  cases x with
  | inl a =>
    show StateT.run ((pure a >>= fun b => pure (Sum.inl b)) : StateT S T (α ⊕ β)) s = _
    simp [StateT.run, StateT.bind, StateT.pure, pure_bind]
  | inr b =>
    show StateT.run ((pure b >>= fun d => pure (Sum.inr d)) : StateT S T (α ⊕ β)) s = _
    simp [StateT.run, StateT.bind, StateT.pure, pure_bind]

theorem stateT_ucMapSum_pure_kleisli {α β γ δ : Type}
    (f : β → StateT S T γ) (g : γ → StateT S T δ) :
    (fun x : α ⊕ β => stateT_ucMapSum pure f x >>= stateT_ucMapSum pure g) =
    stateT_ucMapSum pure (fun b => f b >>= g) := by
  ext x s
  cases x with
  | inl a =>
    show StateT.run (stateT_ucMapSum pure f (.inl a) >>= stateT_ucMapSum pure g) s =
         StateT.run (stateT_ucMapSum pure (fun b => f b >>= g) (.inl a)) s
    simp [stateT_ucMapSum, StateT.run, StateT.bind, StateT.pure, pure_bind, bind_assoc]
  | inr b =>
    show StateT.run (stateT_ucMapSum pure f (.inr b) >>= stateT_ucMapSum pure g) s =
         StateT.run (stateT_ucMapSum pure (fun b => f b >>= g) (.inr b)) s
    simp [stateT_ucMapSum, StateT.run, StateT.bind, StateT.pure, pure_bind, bind_assoc]

end StateT_UCMonadBase

/-! ## Section 3: UCMonadMetric for StateT -/

section StateT_UCMonadMetric

variable {S : Type} {T : Type → Type} [UCMonadMetric T]

/-- Statistical distance for `StateT S T`: delegate to `T` via uncurrying.

    `sdistStateT(f, g) = T.ucSdist(uncurry f, uncurry g)`

    This treats `(input, initial_state)` as a single compound input.
    The result is the worst-case distance over all inputs AND all initial states,
    computed atomically by `T`'s metric. -/
noncomputable def sdistStateT {α β : Type}
    (f g : α → StateT S T β) : ℝ≥0∞ :=
  UCMonadMetric.ucSdist (T := T)
    (fun (p : α × S) => f p.1 p.2)
    (fun (p : α × S) => g p.1 p.2)

theorem sdistStateT_self {α β : Type} (f : α → StateT S T β) :
    sdistStateT f f = 0 :=
  UCMonadMetric.ucSdist_self _

theorem sdistStateT_sym {α β : Type} (f g : α → StateT S T β) :
    sdistStateT f g = sdistStateT g f :=
  UCMonadMetric.ucSdist_sym _ _

theorem sdistStateT_triangle {α β : Type} (f g h : α → StateT S T β) :
    sdistStateT f h ≤ sdistStateT f g + sdistStateT g h :=
  UCMonadMetric.ucSdist_triangle _ _ _

/-- Right PPL for StateT: post-composition doesn't increase distance.

    Proof: `uncurry(f >=> k) = uncurry(f) >=>_T uncurry(k)`,
    so the claim reduces to T's right PPL. -/
theorem sdistStateT_comp_right {α β γ : Type}
    (f g : α → StateT S T β) (k : β → StateT S T γ) :
    sdistStateT (fun a => f a >>= k) (fun a => g a >>= k) ≤ sdistStateT f g := by
  -- StateT bind: (f a >>= k) s = f a s >>= fun (b, s') => k b s'
  -- This is exactly uncurry(f) >=>_T uncurry(k), so T's right PPL applies.
  show UCMonadMetric.ucSdist
    (fun (p : α × S) => (fun a => f a >>= k) p.1 p.2)
    (fun (p : α × S) => (fun a => g a >>= k) p.1 p.2) ≤
    UCMonadMetric.ucSdist
    (fun (p : α × S) => f p.1 p.2)
    (fun (p : α × S) => g p.1 p.2)
  -- (f p.1 >>= k) p.2 = f p.1 p.2 >>= fun (b,s') => k b s' by StateT.bind def
  simp only [StateT.bind]
  exact UCMonadMetric.ucSdist_comp_right _ _ _

/-- Left PPL for StateT: pre-composition with shared prefix doesn't increase distance.

    Proof: `uncurry(m >=> f) = uncurry(m) >=>_T uncurry(f)`,
    so the claim reduces to T's left PPL. -/
theorem sdistStateT_comp_left {α β γ : Type}
    (m : α → StateT S T β) (g₁ g₂ : β → StateT S T γ) :
    sdistStateT (fun a => m a >>= g₁) (fun a => m a >>= g₂) ≤ sdistStateT g₁ g₂ := by
  show UCMonadMetric.ucSdist
    (fun (p : α × S) => (fun a => m a >>= g₁) p.1 p.2)
    (fun (p : α × S) => (fun a => m a >>= g₂) p.1 p.2) ≤
    UCMonadMetric.ucSdist
    (fun (p : β × S) => g₁ p.1 p.2)
    (fun (p : β × S) => g₂ p.1 p.2)
  simp only [StateT.bind]
  exact UCMonadMetric.ucSdist_comp_left _ _ _

end StateT_UCMonadMetric

/-! ## Section 4: Instances -/

/-- `StateT S T` inherits `UCMonadBase` from `T`. -/
noncomputable instance stateT_UCMonadBase {S : Type} {T : Type → Type}
    [UCMonadBase T] : UCMonadBase (StateT S T) where
  ucMapSum := @stateT_ucMapSum S T _
  ucMapSum_inl := stateT_ucMapSum_inl
  ucMapSum_inr := stateT_ucMapSum_inr
  ucMapSum_pure_pure := stateT_ucMapSum_pure_pure
  ucMapSum_pure_kleisli := stateT_ucMapSum_pure_kleisli

/-- `StateT S T` inherits `UCMonadMetric` from `T`.

    The distance is `T.ucSdist` on uncurried functions. Both PPLs hold
    because StateT bind, after uncurrying, IS T bind. -/
noncomputable instance stateT_UCMonadMetric {S : Type} {T : Type → Type}
    [UCMonadMetric T] : UCMonadMetric (StateT S T) where
  ucMapSum := @stateT_ucMapSum S T _
  ucMapSum_inl := stateT_ucMapSum_inl
  ucMapSum_inr := stateT_ucMapSum_inr
  ucMapSum_pure_pure := stateT_ucMapSum_pure_pure
  ucMapSum_pure_kleisli := stateT_ucMapSum_pure_kleisli
  ucSdist := @sdistStateT S T _
  ucSdist_self := sdistStateT_self
  ucSdist_sym := sdistStateT_sym
  ucSdist_triangle := sdistStateT_triangle
  ucSdist_comp_right := sdistStateT_comp_right
  ucSdist_comp_left := sdistStateT_comp_left

/-- `StateT S T` inherits `UCMonadAffine` from `T`. `ucFail` is `T`'s
    `ucFail` lifted into each state, and `ucBind_fail` follows from the
    state-wise application of `T`'s `ucBind_fail`. -/
noncomputable instance stateT_UCMonadAffine {S : Type} {T : Type → Type}
    [UCMonadAffine T] : UCMonadAffine (StateT S T) where
  ucMapSum := @stateT_ucMapSum S T _
  ucMapSum_inl := stateT_ucMapSum_inl
  ucMapSum_inr := stateT_ucMapSum_inr
  ucMapSum_pure_pure := stateT_ucMapSum_pure_pure
  ucMapSum_pure_kleisli := stateT_ucMapSum_pure_kleisli
  ucFail := fun _ => UCMonadAffine.ucFail
  ucBind_fail := by
    intro _ _ c
    funext s
    exact UCMonadAffine.ucBind_fail (c s)

/-- `StateT S T` is a full `UCMonad` — combines the Metric and Affine
    instances above. `UCMonad` has no fields of its own; we wire the
    two parent instances explicitly to break the `UCMonadBase` diamond. -/
noncomputable instance stateT_UCMonad {S : Type} {T : Type → Type}
    [UCMonad T] : UCMonad (StateT S T) :=
  { stateT_UCMonadMetric, stateT_UCMonadAffine with }

/-! ## Section 5: The Para/coPara Interpretation

### Para_S(Kl(T))

The **Para construction** (Capucci–Gavranović 2022) applied to a monoidal
category `C` with an actegory action `⊗ S` produces a new category:
- Objects: same as `C`
- Morphisms `a → b`: `C`-morphisms `(a × S) → (b × S)`

For `C = Kl(T)` with the product actegory:
- `Para_S(Kl(T))(a, b) = (a × S) → T(b × S)`

**Theorem**: `Kl(StateT S T)(a, b) ≅ Para_S(Kl(T))(a, b)`.
The isomorphism is currying/uncurrying.

### coPara(Para_S(Kl(T)))

Applying the coPara construction to `Para_S(Kl(T))` gives:
- 0-cells: `Type`
- 1-cells `hon → out`: `{ iface : Type; prot : (hon × S) → T((out ⊕ iface) × S) }`
- 2-cells P ⟶ Q: `{ sim : (P.iface × S) → T(Q.iface × S); comm : ... }`

This is precisely `ProtBicat(StateT S T)` after uncurrying.

### Connection to Robust Compilation

In `ProtBicat(StateT S T)`, simulators are STATEFUL:
`sim : P.iface → StateT S T Q.iface`. This models secure compilation of
stateful protocols where:
- The compiled program operates in a stateful environment
- The simulator must track state to produce convincing simulation
- The security guarantee is: ∀ stateful adversaries, ∃ stateful simulator

The generic `UCEmulates ↔ RHP` instantiates to `StateT S T`, giving:
**UC emulation for stateful protocols ↔ robust hyperproperty preservation
where both contexts and distinguishers are stateful**.

This provides the formal framework for secure compilation theorems
(Patrignani et al. / Abate et al.) where source and target have state.
-/

section ParaCoPara

variable {S : Type} {T : Type → Type}

/-- Kleisli morphisms of `StateT S T` are in bijection with state-parameterized
    Kleisli morphisms of `T` — the Para construction.

    This is the morphism-level statement of `Kl(StateT S T) ≅ Para_S(Kl(T))`. -/
def klStateT_to_paraKl {α β : Type} (f : α → StateT S T β) :
    (α × S) → T (β × S) :=
  Function.uncurry f

/-- Inverse of the Para isomorphism: curry a T-morphism into a StateT morphism. -/
def paraKl_to_klStateT {α β : Type} (f : (α × S) → T (β × S)) :
    α → StateT S T β :=
  Function.curry f

theorem klStateT_paraKl_roundtrip {α β : Type} (f : α → StateT S T β) :
    paraKl_to_klStateT (klStateT_to_paraKl f) = f := by
  simp [klStateT_to_paraKl, paraKl_to_klStateT, Function.curry_uncurry]

theorem paraKl_klStateT_roundtrip {α β : Type} (f : (α × S) → T (β × S)) :
    klStateT_to_paraKl (paraKl_to_klStateT f) = f := by
  simp [klStateT_to_paraKl, paraKl_to_klStateT, Function.uncurry_curry]

/-- The composition structure is preserved: Kleisli composition in `StateT S T`
    corresponds to Kleisli composition in `T` via uncurrying.

    This is the functoriality of the Para isomorphism. -/
theorem klStateT_comp_eq_paraKl_comp [Monad T] {α β γ : Type}
    (f : α → StateT S T β) (g : β → StateT S T γ) :
    klStateT_to_paraKl (fun a => f a >>= g) =
    fun p => klStateT_to_paraKl f p >>= klStateT_to_paraKl g := by
  funext ⟨a, s⟩; rfl

/-- The `ucSdist` for `StateT S T` equals `T`'s `ucSdist` on Para morphisms. -/
theorem sdistStateT_eq_ucSdist_paraKl [UCMonadMetric T] {α β : Type}
    (f g : α → StateT S T β) :
    sdistStateT f g = UCMonadMetric.ucSdist
      (klStateT_to_paraKl f) (klStateT_to_paraKl g) :=
  rfl

end ParaCoPara

/-! ## Section 6: ProtBicat(StateT S T) as coPara(Para_S(Kl(T)))

    A protocol `P : ProtObj (StateT S T) hon out` has:
    - `P.iface : Type`
    - `P.prot : hon → StateT S T (out ⊕ P.iface) = hon → S → T((out ⊕ P.iface) × S)`

    After uncurrying, this is a 1-cell in `coPara(Para_S(Kl(T)))`.
    Similarly, simulators uncurry to Para morphisms. -/

section ProtBicatUncurry

variable {S : Type} {T : Type → Type} [UCMonadBase T]

/-- Uncurry a ProtObj's protocol to the coPara(Para) form. -/
noncomputable def ProtObj.uncurryProt {hon out : Type}
    (P : ProtObj (StateT S T) hon out) :
    (hon × S) → T ((out ⊕ P.iface) × S) :=
  klStateT_to_paraKl P.prot

/-- Uncurry a ProtMor's simulator to the Para form. -/
noncomputable def ProtMor.uncurrySim {hon out : Type}
    {P Q : ProtObj (StateT S T) hon out}
    (f : ProtMor P Q) :
    (P.iface × S) → T (Q.iface × S) :=
  klStateT_to_paraKl f.sim

end ProtBicatUncurry

/-! ## Section 7: RC for Stateful Protocols

    The generic `UCEmulates ↔ RHP` from `RC.lean` applied to `T = StateT S M`
    gives robust compilation for stateful protocols.

    When instantiated:
    - **Contexts** `ρ : mid → StateT S M out` are stateful subroutines
    - **Distinguishers** `D : β → StateT S M Bool` can read/write state
    - **Simulators** `Sim : leak → StateT S M view` must track state

    This matches the secure compilation setting where both the source and
    target languages are stateful (e.g., compilation of probabilistic programs
    with memory). -/

section StatefulRC

variable {S : Type} {T : Type → Type} [UCMonadMetric T]

/-- In `StateT S T`, UC emulation guarantees security against stateful adversaries.

    The adversary `A : leak → StateT S T view` can read and modify state.
    The simulator `Sim` must similarly maintain state to produce a convincing
    simulation. This is exactly the setting of secure compilation with memory. -/
theorem stateT_adversary_is_stateful
    {hon out iface view : Type} {ε : ℝ≥0∞}
    {π F : hon → StateT S T (out ⊕ iface)}
    (h : UCEmulates (T := StateT S T) (view := view) ε π F) :
    ∀ (A : iface → StateT S T view),
      ∃ (Sim : iface → StateT S T view),
        UCMonadMetric.ucSdist (T := StateT S T)
          (fun a => π a >>= UCMonadBase.ucMapSum pure A)
          (fun a => F a >>= UCMonadBase.ucMapSum pure Sim) ≤ ε := h

end StatefulRC

end UCMonad
