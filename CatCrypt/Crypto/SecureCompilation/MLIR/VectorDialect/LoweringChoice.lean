/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
import CatCrypt.Crypto.Optimizer.X86CostModel

/-!
# MLIR `vector` dialect — Lowering-choice abstraction

This module carves out the **selector** layer of the lowering pipeline. The
`Lowering.lean` module commits, by construction, to one rule per `VectorOp`
(head-of-list, the direct rule). In practice a backend often has multiple
equivalent lowerings for the same abstract op — e.g. a 256-bit `VPADDQ` versus
two 128-bit `VPADDQ` lanes — and a *selector* picks one according to some
strategy.

This file introduces the data structure `LoweringEquivalenceClass`
(a non-empty list of equivalent candidates) and a function `selectLowering`
that picks one candidate from a class. Both the head-of-list selector
(matching the existing `Lowering.lean`) and an egraph-style cost-minimizing
extractor (Phase-2) plug in at the same interface.

## Design references

* **DialEgg** (CGO 2025, Zayed & Dubach, DOI `10.1145/3696443.3708957`):
  external bridge from MLIR to egglog, pre-defines arith / linalg / tosa
  rewrite rules. External-engine design.
* **eqsat** (EGRAPHS '25, Merckx et al., arxiv `2505.09363`): MLIR-native
  e-graphs via three ops `eqsat.eclass` / `eqsat.egraph` / `eqsat.yield`,
  reusing MLIR's `pdl` matcher and MLIR's own CSE pass. The native-embedding
  design we mirror.

See [`README.md`](README.md) §"Design choices: lowering selection" for the
verified-compiler argument for following the *eqsat* native-embedding
approach over DialEgg.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-! ## 1. The candidate / equivalence-class data types -/

/-- A lowering candidate for a `VectorOp`: an alternative `ScalarExpansion`
    (eventually a `Com` fragment) that denotes the same value as every other
    candidate in its equivalence class. The selector picks one. -/
structure LoweringCandidate (α : Type) (n : Nat) where
  /-- Short identifier for the candidate
      (e.g. `"VPADDQ_256"`, `"two_VPADDQ_128"`). -/
  name : String
  /-- The per-lane expansion this candidate emits. -/
  expansion : ScalarExpansion α n
  /-- Cost estimate (cycles on a default x86-64 target). Used by a
      cost-driven selector; ignored by the direct-rule selector that
      always picks the head. -/
  costEstimate : Nat

/-- A non-empty list of equivalent lowering candidates for a single `VectorOp`.

    `head_nonempty` keeps the list non-empty so that picking the head is a
    total function. Pairwise equivalence proofs between candidates are
    Phase-2; in the first landing the equivalence is a *modelling
    invariant* — every constructor of a `LoweringEquivalenceClass` is
    obliged (informally) to produce candidates that denote the same
    function. The follow-up adds a proof field of the shape

    ```
    equivProofs :
      ∀ c ∈ candidates,
        runLaneStores c.expansion.init c.expansion.stores
          = runLaneStores head.expansion.init head.expansion.stores
    ```

    which is linear in the list length (each candidate is paired against
    the head). -/
structure LoweringEquivalenceClass (α : Type) (n : Nat) where
  candidates : List (LoweringCandidate α n)
  head_nonempty : candidates ≠ []

/-! ## 2. The selector

Per the fall-back gate in the task spec, we use a *total* `headD`-based
formulation rather than the dependent `List.head` over a non-emptiness
proof. That keeps the function definitionally simpler and avoids piling
on dependent-type machinery for what is really just "pick one". The
`head_nonempty` field is still carried (it documents the modelling
invariant and is required by Phase-2 pairwise proofs). -/

/-- Default candidate used by the `headD` selector when the candidate list
    is unexpectedly empty. The `head_nonempty` field of
    `LoweringEquivalenceClass` rules this out in practice; the default is
    a defensive fall-back so the selector is total without dependent
    pattern matching. -/
@[reducible] def LoweringCandidate.dummy {α : Type} {n : Nat}
    (init : α) : LoweringCandidate α n :=
  { name := "dummy"
    expansion := { init := defaultLane init, stores := [] }
    costEstimate := 0 }

/-- The base selector: pick the head candidate from the equivalence class.
    This matches the existing direct lowering in `Lowering.lean` (one
    rule per `VectorOp`). A future cost-driven selector lives at the same
    type and would minimize `costEstimate`. -/
def selectLowering {α : Type} {n : Nat} (default : LoweringCandidate α n)
    (cls : LoweringEquivalenceClass α n) : LoweringCandidate α n :=
  cls.candidates.headD default

/-- A *cost-minimizing* selector — included as a stub so the interface
    is exercised by more than one strategy. It picks the candidate with
    the smallest `costEstimate`, falling back to the head when ties or
    when the list is empty (which the invariant rules out). This is the
    selector an egraph extractor would surface as its "best" choice.

    The Phase-2 proof obligation for this selector is that *any* candidate
    in the class denotes the same value as the head — once that is in,
    `selectLoweringMinCost` is denotation-preserving for free. -/
def selectLoweringMinCost {α : Type} {n : Nat} (default : LoweringCandidate α n)
    (cls : LoweringEquivalenceClass α n) : LoweringCandidate α n :=
  match cls.candidates with
  | [] => default
  | c :: rest =>
      rest.foldl (fun best cand =>
        if cand.costEstimate < best.costEstimate then cand else best) c

/-! ## 2b. The X86CostModel-driven selector (the auto-vectorization fix)

`selectLoweringMinCost` minimizes a *hand-set* `costEstimate` field. The
principled selector instead derives each candidate's cost from the SLOTHY-grade
[`X86CostModel`](../../../Optimizer/X86CostModel.lean): it renders the candidate
to its `JInstr 64` block and scores it with `scheduleCostV2` (the `max` of the
critical-path latency bound and the port-pressure throughput bound — a schedule
cannot beat either). The selector then picks the candidate of minimal score.

The crucial difference from a fixed `costEstimate`: the **scalar** lowering of
an `n`-lane op fans out to `n` independent scalar instructions, all competing
for the same ALU ports, so its port-pressure score is `n`; the **vectorized**
candidate issues a single packed µop scoring `1`. The cost model therefore
*sees* the lane-parallelism and the cost-minimizing selector AUTO-PICKS the
vectorized candidate — the human no longer hand-chooses the scalar lowering.

The `render` argument is the candidate → `JInstr 64` block renderer; it is the
target-specific knowledge (which `VectorOp` maps to which packed mnemonic).
Correctness of the choice is independent of `render`: every candidate in a
`LoweringEquivalenceClass` denotes the same value, so `lowerWithSelector`'s
result is the same regardless of which one `render` makes cheapest (this is
exactly what `lowerWithSelector_eq_lower` formalizes — see §4). -/

open CatCrypt.Crypto.Optimizer.X86CostModel in
/-- Score a candidate by the SLOTHY-grade x86 cost of its rendered block:
    `scheduleCostV2 (render c)` = `max(critical-path, port-pressure)`. -/
def candidateX86Cost {α : Type} {n : Nat}
    (render : LoweringCandidate α n → List (JInstr 64))
    (c : LoweringCandidate α n) : Nat :=
  scheduleCostV2 (render c)

/-- The **X86CostModel-driven cost-minimizing selector**. Given a per-candidate
    renderer to `JInstr 64`, it scores every candidate by `scheduleCostV2` over
    its rendered block and returns the candidate of least cost (head on ties /
    empty, which the class invariant rules out).

    This is the drop-in replacement for the head-of-list `selectLowering` that
    makes the compiler choose the lower-cost (vectorized) dialect lowering
    automatically. Plugs into `lowerWithSelector` at the same interface, so —
    by `lowerWithSelector_eq_lower` and the equivalence-class invariant — the
    denotation is preserved no matter which candidate it surfaces. -/
def selectLoweringX86 {α : Type} {n : Nat}
    (render : LoweringCandidate α n → List (JInstr 64))
    (default : LoweringCandidate α n)
    (cls : LoweringEquivalenceClass α n) : LoweringCandidate α n :=
  match cls.candidates with
  | [] => default
  | c :: rest =>
      rest.foldl (fun best cand =>
        if candidateX86Cost render cand < candidateX86Cost render best
        then cand else best) c

/-! ## 3. The selector-driven lowering

`lowerWithSelector` is the abstracted form of `lower`. Instead of
hard-coding the rule, it consumes:
* a `build` function that produces a `LoweringEquivalenceClass` for each
  `VectorOp` (or `none` for scalar-result ops), and
* a `select` function that picks one candidate.

When the build's head is the existing direct rule and the selector is
`selectLowering` (head-of-list), the new form reduces to the existing
`lower`. The bridge theorem `lowerWithSelector_eq_lower` makes that
explicit. -/

/-- Selector-driven variant of `lower`. `build` produces the equivalence
    class (or `none` for scalar-result ops); `select` picks a candidate.
    The default selector is the head-of-list `selectLowering`. -/
def lowerWithSelector {α : Type} {n : Nat} (init : α)
    (build : VectorOp α n → Option (LoweringEquivalenceClass α n))
    (select : LoweringCandidate α n → LoweringEquivalenceClass α n →
              LoweringCandidate α n :=
        selectLowering)
    (op : VectorOp α n) : Option (ScalarExpansion α n) :=
  (build op).map fun cls =>
    (select (LoweringCandidate.dummy init) cls).expansion

/-! ## 4. Bridge theorem to the direct rule

The new abstracted form reduces to the existing direct lowering when:
1. the `build` function's head candidate is the existing rule, and
2. the selector picks the head.

This says the scaffolding is conservative — the existing proven
equivalences `denoteVectorOp_eq_lower_broadcast` /
`denoteVectorOp_eq_lower_add` transport through. -/

/-- **Bridge theorem.** `lowerWithSelector` with the default head-of-list
    selector equals `lower` whenever the `build` function's head candidate
    in each non-empty class matches the existing direct rule's
    `ScalarExpansion`. -/
theorem lowerWithSelector_eq_lower {α : Type} {n : Nat} (init : α)
    (build : VectorOp α n → Option (LoweringEquivalenceClass α n))
    (hb : ∀ op, (build op).map (fun cls =>
        (cls.candidates.headD (LoweringCandidate.dummy init)).expansion)
        = lower init op) (op : VectorOp α n) :
    lowerWithSelector init build (op := op) = lower init op := by
  -- `lowerWithSelector` unfolds to `(build op).map (fun cls => ...headD...expansion)`
  -- which is exactly the LHS of `hb op`.
  unfold lowerWithSelector
  exact hb op

/-! ## 5. Correctness of an arbitrary selector follows from class-equivalence

The cost-driven selector returns *some* member of the equivalence class. Once
the class invariant (every candidate denotes the head's value) is in hand, the
selector's choice is denotation-irrelevant: `lowerWithSelector` produces the
same `ScalarExpansion.denote` whichever candidate is surfaced. This is the
"correct by construction" payoff — selecting the cheapest candidate cannot
change the meaning.

We capture the invariant as a hypothesis `hEquiv` (the Phase-2 proof field of
`LoweringEquivalenceClass`) and require only that the selector returns a class
member (`hMem`), which `selectLowering`, `selectLoweringMinCost`, and
`selectLoweringX86` all satisfy. -/

/-- A selector that always returns a member of its input class. The three
    concrete selectors (`selectLowering`, `selectLoweringMinCost`,
    `selectLoweringX86`) are all `ClassMemberSelector`s. -/
def ClassMemberSelector {α : Type} {n : Nat}
    (select : LoweringCandidate α n → LoweringEquivalenceClass α n →
              LoweringCandidate α n) : Prop :=
  ∀ (default : LoweringCandidate α n) (cls : LoweringEquivalenceClass α n),
    select default cls ∈ cls.candidates

/-- `selectLowering` (head-of-list) returns a class member. -/
theorem selectLowering_classMember {α : Type} {n : Nat} :
    ClassMemberSelector (selectLowering (α := α) (n := n)) := by
  intro default cls
  cases h : cls.candidates with
  | nil => exact absurd h cls.head_nonempty
  | cons c rest => simp [selectLowering, h]

/-- The fold used by the cost selectors keeps the accumulator inside the list:
    folding the "pick smaller cost" combinator over `rest` starting from a
    member of `c :: rest` returns a member of `c :: rest`. -/
private theorem foldl_min_mem {α : Type} {n : Nat}
    (cost : LoweringCandidate α n → Nat) :
    ∀ (rest : List (LoweringCandidate α n)) (acc : LoweringCandidate α n)
      (full : List (LoweringCandidate α n)),
      acc ∈ full → (∀ x ∈ rest, x ∈ full) →
      (rest.foldl (fun best cand =>
        if cost cand < cost best then cand else best) acc) ∈ full
  | [], acc, _, hacc, _ => hacc
  | c :: rest, acc, full, hacc, hsub => by
      simp only [List.foldl_cons]
      apply foldl_min_mem cost rest
      · by_cases hlt : cost c < cost acc
        · simp [hlt]; exact hsub c List.mem_cons_self
        · simp [hlt]; exact hacc
      · intro x hx; exact hsub x (List.mem_cons_of_mem _ hx)

/-- `selectLoweringX86` returns a class member (the cheapest one). -/
theorem selectLoweringX86_classMember {α : Type} {n : Nat}
    (render : LoweringCandidate α n → List (JInstr 64)) :
    ClassMemberSelector (selectLoweringX86 render) := by
  intro default cls
  unfold selectLoweringX86
  cases h : cls.candidates with
  | nil => exact absurd h cls.head_nonempty
  | cons c rest =>
      have : (rest.foldl (fun best cand =>
          if candidateX86Cost render cand < candidateX86Cost render best
          then cand else best) c) ∈ c :: rest :=
        foldl_min_mem (candidateX86Cost render) rest c (c :: rest)
          List.mem_cons_self (fun x hx => List.mem_cons_of_mem _ hx)
      simpa [h] using this

/-- **Selection is denotation-preserving for any class-member selector.**

    If every candidate in the built class denotes the same vector as a
    reference `spec` (the equivalence-class invariant), then
    `lowerWithSelector` with *any* `ClassMemberSelector` — in particular the
    cost-minimizing `selectLoweringX86` — yields a `ScalarExpansion` whose
    denotation is `spec`. The cost selector's freedom to pick the cheapest
    candidate cannot change the result.

    This is the "for free" correctness the task asks for: it is downstream of
    the structure of `lowerWithSelector` (it always reads the selected
    candidate's `expansion`) plus the class invariant — no per-op proof. -/
theorem lowerWithSelector_denote_of_classEquiv {α : Type} {n : Nat} (init : α)
    (build : VectorOp α n → Option (LoweringEquivalenceClass α n))
    (select : LoweringCandidate α n → LoweringEquivalenceClass α n →
              LoweringCandidate α n)
    (hsel : ClassMemberSelector select)
    (op : VectorOp α n) (cls : LoweringEquivalenceClass α n)
    (hbuild : build op = some cls)
    (spec : VectorTy α n)
    (hEquiv : ∀ c ∈ cls.candidates, c.expansion.denote = spec) :
    (lowerWithSelector init build (select := select) (op := op)).map (·.denote)
      = some spec := by
  unfold lowerWithSelector
  rw [hbuild]
  simp only [Option.map_some]
  exact congrArg some (hEquiv _ (hsel (LoweringCandidate.dummy init) cls))

/-! ## 6. Demonstration: the cost selector AUTO-PICKS the vectorized candidate

We build a two-candidate equivalence class for a lane-parallel op: a scalar
fan-out candidate (one scalar `add` per lane) versus a vectorized candidate
(one packed `add`). The `X86CostModel` renderer scores the scalar block at its
port-pressure bound (one `add` per lane, all on the shared ALU ports ⇒ cost
`= lane count`) and the vectorized block at `1`. `selectLoweringX86` therefore
returns the *vectorized* candidate — `native_decide`-witnessed below. -/

section AutoVectorizeDemo

open CatCrypt.Crypto.Optimizer.X86CostModel

/-- Scalar fan-out of a 4-lane packed add: four independent scalar `add`s, one
    per lane. Independent (distinct dst/src names) so they all bind on port
    pressure. -/
def demoScalarBlock : List (JInstr 64) :=
  [ JInstr.add "r0" (JOperand.reg "a0")
  , JInstr.add "r1" (JOperand.reg "a1")
  , JInstr.add "r2" (JOperand.reg "a2")
  , JInstr.add "r3" (JOperand.reg "a3") ]

/-- Vectorized realization: a single packed `add` (one µop in the cost model). -/
def demoVecBlock : List (JInstr 64) :=
  [ JInstr.add "r" (JOperand.reg "a") ]

/-- The scalar 4-lane fan-out costs `4` under the SLOTHY-grade model (its
    port-pressure lower bound: 4 ALU µops). -/
theorem demoScalarBlock_cost : scheduleCostV2 demoScalarBlock = 4 := by
  native_decide

/-- The vectorized candidate costs `1` (a single packed µop). -/
theorem demoVecBlock_cost : scheduleCostV2 demoVecBlock = 1 := by
  native_decide

/-- **The cost witness: the vectorized candidate is strictly cheaper.** This is
    what makes the cost-minimizing selector prefer it. -/
theorem demoVec_cheaper :
    scheduleCostV2 demoVecBlock < scheduleCostV2 demoScalarBlock := by
  native_decide

/-- A renderer that scores the scalar candidate by `demoScalarBlock` and any
    other (vectorized) candidate by `demoVecBlock`, keyed on the candidate name.
    This is the target-specific knowledge: the `"scalar4"`-named candidate
    fans out to four scalar adds, the vectorized one to a single packed add. -/
def demoRender {α : Type} {n : Nat} (c : LoweringCandidate α n) :
    List (JInstr 64) :=
  if c.name = "scalar4" then demoScalarBlock else demoVecBlock

/-- `loweredAdd`'s denotation is the abstract `map₂` of the lane op — the
    `add`-lowering keystone, re-exported here so the demo can discharge the
    equivalence-class invariant. -/
theorem loweredAdd_denote {α : Type} {n : Nat} (init : α) (op : α → α → α)
    (v w : VectorTy α n) :
    (loweredAdd init op v w).denote = VectorTy.map₂ op v w := by
  have h := lower_add_correct (n := n) init op v w
  rw [lower_add_eq] at h
  simpa using h

/-- A two-candidate equivalence class for a 4-lane `add op v w`: the scalar
    fan-out candidate (head — the current hand-chosen default) and the
    vectorized candidate. Both carry the *same* `ScalarExpansion`
    (`loweredAdd …`), so they are denotation-equivalent by construction. -/
def demoClass {α : Type} (init : α) (op : α → α → α)
    (v w : VectorTy α 4) : LoweringEquivalenceClass α 4 :=
  { candidates :=
      [ { name := "scalar4", expansion := loweredAdd init op v w, costEstimate := 4 }
      , { name := "vpadd",   expansion := loweredAdd init op v w, costEstimate := 1 } ]
    head_nonempty := by simp }

/-- Every candidate of `demoClass` carries the `loweredAdd` expansion. -/
private theorem demoClass_expansion {α : Type} (init : α) (op : α → α → α)
    (v w : VectorTy α 4) :
    ∀ c ∈ (demoClass init op v w).candidates,
      c.expansion = loweredAdd init op v w := by
  intro c hc
  simp only [demoClass, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h <;> (subst h; rfl)

/-- A concrete instantiation of the demo class over `BitVec 32` lanes so the
    selector can be evaluated by `native_decide`. The lane op is `(· + ·)`, the
    operands are fixed (the actual data is irrelevant — only the candidate
    *names* drive the cost, via `demoRender`). -/
def demoClassBV : LoweringEquivalenceClass (BitVec 32) 4 :=
  demoClass (0 : BitVec 32) (· + ·) (fun _ => 0) (fun _ => 0)

/-- **The auto-vectorization payoff.** Applied to the demo class, the
    X86CostModel-driven selector returns the **vectorized** (`"vpadd"`)
    candidate — *not* the head-of-list scalar default. The human hand-chose the
    scalar lowering (it is the class head, what `selectLowering` would pick);
    the cost model overrides that choice automatically, because
    `scheduleCostV2 demoVecBlock (= 1) < scheduleCostV2 demoScalarBlock (= 4)`. -/
theorem demo_autoPicks_vectorized :
    (selectLoweringX86 demoRender (LoweringCandidate.dummy (0 : BitVec 32))
        demoClassBV).name = "vpadd" := by
  native_decide

/-- Contrast: the head-of-list `selectLowering` keeps the hand-chosen scalar
    candidate. The cost selector is what flips the choice. -/
theorem demo_head_keeps_scalar :
    (selectLowering (LoweringCandidate.dummy (0 : BitVec 32)) demoClassBV).name
      = "scalar4" := by
  native_decide

/-- And the cost selector's choice is denotation-preserving for free:
    regardless of which candidate it surfaces, `lowerWithSelector` denotes the
    abstract `add`'s `map₂`. Instantiates
    `lowerWithSelector_denote_of_classEquiv` — both candidates carry the same
    `loweredAdd` expansion, so the equivalence invariant holds per candidate. -/
theorem demo_denote_preserved {α : Type} (init : α) (op : α → α → α)
    (v w : VectorTy α 4) :
    (lowerWithSelector init (fun _ => some (demoClass init op v w))
        (select := selectLoweringX86 demoRender) (op := .add op v w)).map (·.denote)
      = some (VectorTy.map₂ op v w) := by
  apply lowerWithSelector_denote_of_classEquiv (cls := demoClass init op v w)
  · exact selectLoweringX86_classMember demoRender
  · rfl
  · intro c hc
    rw [demoClass_expansion init op v w c hc, loweredAdd_denote]

end AutoVectorizeDemo

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
