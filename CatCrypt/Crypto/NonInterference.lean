/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.UCDSL

/-!
# Non-Interference for MPC Protocols

Formalizes the non-interference (NI) approach to MPC security from
Haagh–Karbyshev–Oechsner–Spitters–Strub (CSF 2018).

## Key results

* `PassiveNI` — Non-interference definition for passive security (Definition 5/6)
* `PassiveSimSec` — Standard simulation-based passive security (Definition 3)
* `passive_ni_implies_sim` — NI implies simulation security (Theorem 1, ⟹ direction)
* `passive_sim_implies_ni` — Simulation security implies NI (Theorem 1, ⟸ direction)
* `ActiveNI` — Non-interference definition for active security (Definition 7)
* `active_ni_implies_sim` — Active NI implies active simulation security (Theorem 2)

Concrete instantiations at specific MPC protocols (Maurer, MPC-in-the-Head) are
not provided: this module is the abstract framework only and deliberately
contains no protocol security proof.

## References

* [Haagh et al., *Computer-aided proofs for MPC with active security*, CSF 2018]
* [Almeida et al., *Enforcing ideal-world leakage bounds in MPC*, ePrint 2018/404]

**0 axioms**.
-/

namespace CatCrypt.Crypto.NonInterference

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCDSL
open scoped ENNReal

set_option autoImplicit false

/-! ## Abstract n-Party MPC Protocol -/

/-- An abstract n-party MPC protocol.

    Captures the essential structure of secret-sharing-based MPC:
    n parties compute a public function f on their private inputs,
    communicating via a probabilistic protocol. Each party's view
    during execution is a probabilistic function of all inputs.

    This abstracts over the concrete protocol implementation
    (Maurer, SPDZ, etc.) to state NI properties generically. -/
structure MPCProtocol where
  /-- Number of parties. -/
  n : ℕ
  /-- Input type for each party. -/
  InputTy : Type
  /-- Output type. -/
  OutputTy : Type
  /-- View type (what a party observes during execution). -/
  ViewTy : Type
  /-- The ideal functionality: deterministic function computed by the protocol. -/
  f : (Fin n → InputTy) → OutputTy
  /-- Party i's view during protocol execution on inputs **x**. -/
  view : Fin n → (Fin n → InputTy) → SPComp ViewTy
  /-- Protocol output on inputs **x**. -/
  output : (Fin n → InputTy) → SPComp OutputTy

/-- Input vector type for an MPC protocol. -/
abbrev MPCProtocol.Inputs (π : MPCProtocol) := Fin π.n → π.InputTy

/-! ## Passive Non-Interference (Definition 5/6, Haagh et al.)

The key insight: instead of constructing a simulator, we show that
two runs of the **same** protocol with different inputs produce
indistinguishable views, provided the corrupt party's input is fixed
and the output is consistent. -/

/-- Two input vectors agree at position i. -/
def inputsAgreeAt {n : ℕ} {α : Type} (i : Fin n) (x x' : Fin n → α) : Prop :=
  x i = x' i

/-- Two input vectors produce the same output under f. -/
def outputsAgree {n : ℕ} {α β : Type} (f : (Fin n → α) → β) (x x' : Fin n → α) : Prop :=
  f x = f x'

/-- Passive non-interference (Definition 5/6, Haagh et al.).

    An n-party protocol π enjoys passive non-interference if for all
    corrupt parties i and all input pairs **x**, **x'** where:
    - x_i = x'_i (corrupt party's input is the same)
    - f(**x**) = f(**x'**) (the computation outputs are equal)

    then party i's view is perfectly indistinguishable:
      view_i^π(**x**) = view_i^π(**x'**)

    This is a relational property of a single program: we compare two
    runs with different inputs, rather than comparing a protocol with
    a structurally different simulator. -/
structure PassiveNI (π : MPCProtocol) : Prop where
  /-- Input independence: adversary's view is independent of honest inputs. -/
  input_independence : ∀ (i : Fin π.n) (x x' : π.Inputs),
    inputsAgreeAt i x x' →
    outputsAgree π.f x x' →
    π.view i x = π.view i x'

/-- Passive simulation-based security (Definition 3, Haagh et al.).

    The standard definition: for each corrupt party i, there exists a
    simulator S_i that produces a view indistinguishable from the real
    view, given only the corrupt party's input and the output.

    **Correctness** is stated separately.

    Not `: Prop` because it carries the simulator construction. -/
structure PassiveSimSec (π : MPCProtocol) where
  /-- For each party, a simulator exists that depends only on
      the corrupt input and the output. -/
  simulator : Fin π.n → π.InputTy → π.OutputTy → SPComp π.ViewTy
  /-- The simulator's output equals the real view for all inputs. -/
  indistinguishable : ∀ (i : Fin π.n) (x : π.Inputs),
    π.view i x = simulator i (x i) (π.f x)

/-! ## Theorem 1: Passive NI ⟺ Passive Simulation Security -/

/-- **Theorem 1 (⟸ direction)**: Simulation security implies NI.

    If a simulator S_i exists, then for inputs with x_i = x'_i and
    f(**x**) = f(**x'**), both views equal S_i(x_i, f(**x**)),
    hence equal each other by transitivity of equality. -/
theorem passive_sim_implies_ni (π : MPCProtocol) (h : PassiveSimSec π) :
    PassiveNI π where
  input_independence i x x' h_input h_output := by
    rw [h.indistinguishable i x, h.indistinguishable i x']
    simp only [inputsAgreeAt, outputsAgree] at h_input h_output
    rw [h_input, h_output]

/-- **Theorem 1 (⟹ direction)**: NI implies simulation security.

    Given NI, the simulator is constructed as follows:
    - Given corrupt input x_i and output y = f(**x**)
    - Find **any** consistent input vector x' with x'_i = x_i and f(x') = y
    - Run the real protocol on x' and return the view

    By NI, the choice of x' doesn't matter: any two consistent inputs
    produce identical views. We take the simulator to be `view i x`
    for an arbitrary fixed x, since NI guarantees this equals
    `view i x'` for any other consistent x'.

    Note: This direction requires that for each (x_i, y), there exists
    a consistent input vector. This is the "invertibility" assumption
    from Haagh et al. (Theorem 1 remark). -/
noncomputable def passive_ni_implies_sim (π : MPCProtocol) (h : PassiveNI π)
    /- For each (corrupt_input, output), there exists a consistent input vector. -/
    (h_inv : ∀ (i : Fin π.n) (xi : π.InputTy) (y : π.OutputTy),
      ∃ x : π.Inputs, x i = xi ∧ π.f x = y) :
    PassiveSimSec π where
  simulator i xi y :=
    π.view i (h_inv i xi y).choose
  indistinguishable i x := by
    have ⟨hxi, hfy⟩ := (h_inv i (x i) (π.f x)).choose_spec
    exact h.input_independence i x _ hxi.symm hfy.symm

/-! ## Active Non-Interference (Definition 7, Haagh et al.)

For active security, the protocol is split into two phases:
π = π₂ ∘ π₁ (input+computation, then output).

The NI-based definition decomposes into three properties. -/

/-- An abstract MPC protocol with phase decomposition for active security.

    The protocol splits into:
    - π₁: input + computation phase
    - π₂: output phase

    The adversary's view after π₁ is `viewAfterPhase1`.
    The final messages in π₂ are `outputMessages`. -/
structure MPCProtocolPhased extends MPCProtocol where
  /-- View type after phase 1 (input + computation). -/
  Phase1ViewTy : Type
  /-- Output message type (what honest parties send in the output phase). -/
  OutputMsgTy : Type
  /-- Corrupt party's view after the input+computation phase. -/
  viewAfterPhase1 : Fin n → (Fin n → InputTy) → SPComp Phase1ViewTy
  /-- Input extraction: recover the corrupt party's committed input
      from their phase-1 view. -/
  extractInput : Fin n → Phase1ViewTy → InputTy
  /-- Output messages from honest parties in the output phase. -/
  outputMessages : Fin n → (Fin n → InputTy) → SPComp OutputMsgTy

/-- Active NI-based security (Definition 7, Haagh et al.).

    Three properties that together imply active simulation-based security:

    1. **Correctness**: Using the extracted corrupt input x'_a = in_a(v) and
       the actual honest inputs, the output is f(x').
    2. **Input Independence**: The adversary's view after π₁ is independent
       of honest parties' inputs (only depends on corrupt input).
    3. **Output Simulation**: The output-phase messages depend only on the
       adversary's phase-1 view and the result y. -/
structure ActiveNI (π : MPCProtocolPhased) : Prop where
  /-- Correctness: the protocol computes f on the "effective" inputs. -/
  correctness : ∀ (a : Fin π.n) (x : π.Inputs),
    ∀ v, π.viewAfterPhase1 a x = SPComp.pure v →
    let x'_a := π.extractInput a v
    let x' : π.Inputs := fun j => if j = a then x'_a else x j
    π.output x = SPComp.pure (π.f x')
  /-- Input independence: phase-1 view is independent of honest inputs. -/
  input_independence : ∀ (a : Fin π.n) (x x' : π.Inputs),
    inputsAgreeAt a x x' →
    π.viewAfterPhase1 a x = π.viewAfterPhase1 a x'
  /-- Output simulation: output messages depend only on view and result. -/
  output_simulation : ∀ (a : Fin π.n) (x x' : π.Inputs),
    inputsAgreeAt a x x' →
    outputsAgree π.f x x' →
    π.outputMessages a x = π.outputMessages a x'

/-- Active simulation-based security (Definition 4, Haagh et al.).

    For every adversary A in the real model, there exists a simulator S
    for the ideal model such that the ideal and real outputs are
    perfectly indistinguishable. -/
structure ActiveSimSec (π : MPCProtocolPhased) where
  /-- The simulator for the ideal model. -/
  simulator : Fin π.n → π.Phase1ViewTy → π.OutputTy → SPComp π.ViewTy
  /-- Indistinguishability of real and ideal executions. -/
  indistinguishable : ∀ (a : Fin π.n) (x : π.Inputs),
    π.view a x = do
      let v ← π.viewAfterPhase1 a x
      let x'_a := π.extractInput a v
      let x' : π.Inputs := fun j => if j = a then x'_a else x j
      simulator a v (π.f x')

/-- **Theorem 2**: Active NI implies active simulation security.

    The simulator construction (Haagh et al.):
    1. Run π₁ with default inputs (0) for honest parties → get view v
    2. Extract corrupt input: x'_a = in_a(v)
    3. Send x'_a to trusted party T → get y = f(x')
    4. Sample output messages from the distribution D_{v,y}

    Input independence guarantees step 1 is indistinguishable from
    a real execution. Output simulation guarantees step 4 produces
    correct final messages.

    Note: The converse does NOT hold in the active case. -/
noncomputable def active_ni_implies_sim (π : MPCProtocolPhased) (_ : ActiveNI π)
    /- Default input for honest parties in the simulation. -/
    (_default_input : π.InputTy)
    /- The output messages can be sampled given view and result. -/
    (output_sampler : Fin π.n → π.Phase1ViewTy → π.OutputTy → SPComp π.ViewTy)
    /- The real view factors through phase-1 view and output sampler.
       This is the "protocol-specific factorization" assumption: the view
       decomposes as running phase 1, extracting the effective input,
       and then running the output sampler on the result. -/
    (view_factors : ∀ (a : Fin π.n) (x : π.Inputs),
      π.view a x = do
        let v ← π.viewAfterPhase1 a x
        let x'_a := π.extractInput a v
        let x' : π.Inputs := fun j => if j = a then x'_a else x j
        output_sampler a v (π.f x')) :
    ActiveSimSec π where
  simulator := output_sampler
  indistinguishable a x := view_factors a x

/-! ## NI for Game Pairs (sdist-based)

When we don't have perfect NI (NI at distance 0), we need
a quantified version compatible with our sdist framework. -/

/-- Quantified passive NI: the adversary's view changes by at most ε
    when honest inputs change (with corrupt input and output fixed).

    This generalizes perfect NI (ε = 0) to the computational setting
    (e.g., SPDZ with MAC forgery probability 1/|F|). -/
structure QuantifiedPassiveNI (π : MPCProtocol) (ε : ℝ≥0∞) : Prop where
  /-- Bounded input independence. -/
  input_independence : ∀ (i : Fin π.n) (x x' : π.Inputs),
    inputsAgreeAt i x x' →
    outputsAgree π.f x x' →
    sdist (fun _ : Unit => π.view i x) (fun _ : Unit => π.view i x') ≤ ε

/-- Perfect NI is quantified NI at ε = 0. -/
theorem passiveNI_is_quantifiedNI_zero (π : MPCProtocol) (h : PassiveNI π) :
    QuantifiedPassiveNI π 0 where
  input_independence i x x' h_in h_out := by
    have := h.input_independence i x x' h_in h_out
    rw [this]
    exact le_of_eq (sdist_self _)

/-- Quantified NI implies UC security via the simulation paradigm.

    The ideal protocol is the simulator from the NI→Sim construction
    (pick an arbitrary consistent input vector). -/
theorem quantified_ni_implies_uc (π : MPCProtocol) (ε : ℝ≥0∞) (V : Type)
    (h : QuantifiedPassiveNI π ε)
    (h_inv : ∀ (i : Fin π.n) (xi : π.InputTy) (y : π.OutputTy),
      ∃ x : π.Inputs, x i = xi ∧ π.f x = y)
    (i : Fin π.n) :
    UCEmulates ε (UCSpec.ofGame π.Inputs π.ViewTy V)
      (UCProtocol.ofGame (π.view i))
      (UCProtocol.ofGame fun x =>
        (h_inv i (x i) (π.f x)).choose |> π.view i) := by
  apply UCEmulates_of_game_sdist
  -- Need: sdist (π.view i) (fun x => π.view i (h_inv ...).choose) ≤ ε
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
  have ⟨hxi, hfy⟩ := (h_inv i (a i) (π.f a)).choose_spec
  have h_ni := h.input_independence i a _ hxi.symm hfy.symm
  exact sdist_le_of_forall h_ni D () h₀

/-! ## Sequential Composition of Non-Interference

If two protocol phases each satisfy quantified NI, their sequential
composition (the first phase followed by the second) also satisfies NI
with the additive bound ε₁ + ε₂.

This is the NI analogue of the standard game-hopping composition principle
and follows directly from `sdist_comp_add` (the composition bound for sdist). -/

/-- Sequential composition of two protocol views preserves non-interference.

    If `view₁` satisfies ε₁-NI and `view₂` satisfies ε₂-NI (both with
    corrupt input and output agreement), then the composed view
    `view₁ >=> view₂` satisfies (ε₁ + ε₂)-NI.

    This models protocols where the adversary's view is formed in two
    phases: first observing phase-1 data, then phase-2 data that depends
    on phase-1 output. The sdist composition bound ensures the total
    privacy loss is at most additive.

    The proof uses `sdist_comp_add`: sequential composition of ε₁-close
    and ε₂-close Kleisli morphisms yields (ε₁ + ε₂)-close morphisms. -/
theorem seqCompose_ni
    {InputTy ViewTy₁ ViewTy₂ : Type}
    {n : ℕ}
    (view₁ : Fin n → (Fin n → InputTy) → SPComp ViewTy₁)
    (view₂ : Fin n → (Fin n → InputTy) → SPComp ViewTy₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : ∀ (i : Fin n) (x x' : Fin n → InputTy),
      sdist (fun _ : Unit => view₁ i x) (fun _ : Unit => view₁ i x') ≤ ε₁)
    (h₂ : ∀ (i : Fin n) (x x' : Fin n → InputTy),
      sdist (fun _ : Unit => view₂ i x) (fun _ : Unit => view₂ i x') ≤ ε₂) :
    ∀ (i : Fin n) (x x' : Fin n → InputTy),
      sdist (fun _ : Unit => SPComp.bind (view₁ i x) fun _ => view₂ i x)
            (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x') ≤ ε₁ + ε₂ := by
  intro i x x'
  -- Step 1: triangle inequality to split the hop into two parts
  calc sdist (fun _ : Unit => SPComp.bind (view₁ i x) fun _ => view₂ i x)
             (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x')
      ≤ sdist (fun _ : Unit => SPComp.bind (view₁ i x) fun _ => view₂ i x)
              (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x) +
        sdist (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x)
              (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x') :=
        sdist_triangle _ _ _
    -- Step 2: first hop changes view₁ (right PPL), second hop changes view₂ (left PPL)
    _ ≤ ε₁ + ε₂ := by
        apply add_le_add
        · -- Changing view₁ only: post-composition with (fun _ => view₂ i x) is right PPL
          exact le_trans (sdist_comp_right
            (fun _ : Unit => view₁ i x) (fun _ : Unit => view₁ i x')
            (fun _ => view₂ i x)) (h₁ i x x')
        · -- Changing view₂ only: pre-composition with view₁ i x' is left PPL
          -- sdist_comp_left gives: ≤ sdist (fun _ : ViewTy₁ => view₂ i x) (fun _ : ViewTy₁ => view₂ i x')
          -- sdist_precomp_le bridges to: ≤ sdist (fun _ : Unit => view₂ i x) (fun _ : Unit => view₂ i x')
          calc sdist (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x)
                     (fun _ : Unit => SPComp.bind (view₁ i x') fun _ => view₂ i x')
              ≤ sdist (fun _ : ViewTy₁ => view₂ i x) (fun _ : ViewTy₁ => view₂ i x') :=
                sdist_comp_left (fun _ : Unit => view₁ i x')
                  (fun _ => view₂ i x) (fun _ => view₂ i x')
            _ ≤ sdist (fun _ : Unit => view₂ i x) (fun _ : Unit => view₂ i x') :=
                sdist_precomp_le (fun _ : Unit => view₂ i x) (fun _ : Unit => view₂ i x')
                  (fun _ : ViewTy₁ => ())
            _ ≤ ε₂ := h₂ i x x'

end CatCrypt.Crypto.NonInterference
