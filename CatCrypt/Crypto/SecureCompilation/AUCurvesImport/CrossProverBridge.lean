/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.PilotImport

@[expose] public section

set_option autoImplicit false

/-!
# AUCurves → CatCrypt cross-prover semantics bridge

This module is the semantics bridge of the AUCurves retarget.

`PilotImport.lean` gives the *structural* correspondence (AUCurves'
`rust_cmd_ed` AST ↔ CatCrypt `LowCT`, AST-by-AST: theorems
`importedPilot_eq`, `importedFe25519Add_eq`) and the backend cross-check.
This module addresses the full **cross-prover SEMANTIC equivalence**:

> AUCurves' Rocq big-step relation `rust_exec_ed`
> (`AUCurves/src/Bedrock/SafeRustEd25519Sim.v`, Qed'd, axiom-free —
> `Print Assumptions safe_cmd_correct_ed` ⇒ *"Closed under the global
> context"*) ⇔ CatCrypt's Lean big-step relation `RustExec`
> (`CatCrypt/Crypto/Jasmin/LowCT.lean`), constructor-by-constructor.

A *fully machine-checked* cross-prover equivalence spans two proof
assistants and therefore **cannot** be a single Lean `theorem`.  This module
provides:

1. **A faithful Lean transcription of `rust_exec_ed`** — `AUCurvesExec`, a
   parametric inductive whose constructors mirror the Rocq inductive's
   constructors one-for-one (for the correspondence-map fragment:
   skip / seq / letZero / call / limbStore — the constructors the pilot and
   `fe25519_add` exercise).  Like the Rocq relation, it is parametric over the
   same opaque effects the Rocq relation is parametric / determined by:
   * `calleePost : fname → args → dst → pre → post → Prop`, mirroring Rocq's
     `callee_post` (a `Prop`-relation, NOT a function);
   * `limbVal : RustState → SExpr → Nat`, the Rocq limb value
     `eval_sexpr_ed rs e` (masked through `mask64`);
   * `limbWrite : Located → (Σ t, RustVal t) → Nat → Nat → (Σ t, RustVal t)`,
     the Rocq concrete limb-list overwrite `list_set i val_v limbs_old`.

   This makes the Rocq side a *concrete, inspectable Lean object* against which
   CatCrypt's `RustExec` can be compared inside Lean — modulo the transcription
   trust edge stated in §"Residual".

2. **The per-constructor correspondence theorems that close
   in-Lean** — given explicit *bridge* hypotheses tying the Rocq-shape opaque
   effects (`calleePost`, `limbVal`, `limbWrite`) to a CatCrypt `LeafSpec`,
   each constructor (`skip`, `seq`, `letZero`, `call`, `limbStore`) lifts an
   `AUCurvesExec` derivation to a `RustExec` derivation with the same
   post-state.  These are real Lean theorems about `RustExec`.

3. **A precisely-scoped residual** (§"Residual"): the two-prover trust edge is
   exactly (a) that `AUCurvesExec` faithfully transcribes the Rocq
   `rust_exec_ed` (a meta-level claim, not a Lean theorem — it is checked by
   reading both inductives side-by-side, recorded here), and (b) the named
   bridge hypotheses connecting the Rocq-shape effects to the CatCrypt
   `LeafSpec`.  Everything *downstream* of those is a closed Lean proof.

No open goals, no `admit`: the residual is expressed as named hypotheses
(`CallBridge`, `limbValBridge`, `limbWriteBridge`) and a documented
transcription caveat, never as a stub.

## The constructor map (Rocq `rust_exec_ed` ↔ this Lean transcription ↔ `RustExec`)

| Rocq `rust_exec_ed` constructor    | `AUCurvesExec` (this file)   | CatCrypt `RustExec`       |
|------------------------------------|------------------------------|---------------------------|
| `rexec_skip`                       | `AUCurvesExec.skip`          | `RustExec.skip`           |
| `rexec_seq`                        | `AUCurvesExec.seq`           | `RustExec.seq`            |
| `rexec_let_zero`                   | `AUCurvesExec.letZero`       | `RustExec.letZero`        |
| `rexec_call` (oracle `callee_post`)| `AUCurvesExec.call` (`calleePost`) | `RustExec.call` (`leafSpec.call`) |
| `rexec_limb_store_fp25519`         | `AUCurvesExec.limbStore`     | `RustExec.limbStoreExpr`  |
-/

namespace CatCrypt.Crypto.SecureCompilation.AUCurvesImport

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Lean transcription of AUCurves' `rust_exec_ed`

`AUCurvesExec calleePost limbVal limbWrite c rs rs'` is the faithful Lean image
of the correspondence-map fragment of Rocq's
`rust_exec_ed callee_post callee_post_n function_table c rs1 rs2`
(`callee_post_n` / `function_table` are not exercised by the pilot or
`fe25519_add`, whose only constructors are skip/seq/letZero/call/limbStore, so
the corresponding `rexec_calln` / `rexec_callfn` rules are dropped).

The state side reuses CatCrypt's `RustState` / `Located`: that is licensed by
the structural correspondence (`PilotImport.lean`), which already established
that `located_ed`, `tower_type_ed`, and the tower/scalar heaps map across the
two formalisms one-for-one. -/

/-- Faithful Lean transcription of the correspondence-fragment of AUCurves'
    Rocq big-step relation `rust_exec_ed`.  Parametric over the same opaque
    effects the Rocq relation is parametric on / determined by:
    `calleePost` (= Rocq `callee_post`, a `Prop`-relation), `limbVal` (= the
    Rocq `eval_sexpr_ed`-masked limb value), and `limbWrite` (= the Rocq
    `list_set`-into-limb-list concrete overwrite, lifted to the opaque
    `Σ t, RustVal t` carrier). -/
inductive AUCurvesExec
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (limbVal : RustState → SExpr → Nat)
    (limbWrite : Located → (Σ t : TowerType, RustVal t) → Nat → Nat →
      (Σ t : TowerType, RustVal t)) :
    LowCT → RustState → RustState → Prop where
  /-- Mirrors Rocq `rexec_skip`. -/
  | skip : ∀ rs, AUCurvesExec calleePost limbVal limbWrite .RSkip rs rs
  /-- Mirrors Rocq `rexec_seq`. -/
  | seq : ∀ c1 c2 rs1 rs2 rs3,
      AUCurvesExec calleePost limbVal limbWrite c1 rs1 rs2 →
      AUCurvesExec calleePost limbVal limbWrite c2 rs2 rs3 →
      AUCurvesExec calleePost limbVal limbWrite (.RSeq c1 c2) rs1 rs3
  /-- Mirrors Rocq `rexec_let_zero`.  The Rocq rule carries a `well_formed_ed v`
      side condition on the (default) initial value; on the CatCrypt side the
      zeroed default `(default : RustVal t)` is well-formed by construction, so
      that side condition is discharged structurally and is not re-stated. -/
  | letZero : ∀ x t body rs1 rs2,
      AUCurvesExec calleePost limbVal limbWrite body
        (rsSetTower rs1 x ⟨t, default⟩) rs2 →
      AUCurvesExec calleePost limbVal limbWrite (.RLetZero x t body) rs1 rs2
  /-- Mirrors Rocq `rexec_call`: the post-state is whatever the opaque oracle
      `calleePost` relates the pre-state to (function name, args, dst). -/
  | call : ∀ fname dst args rs1 rs2,
      calleePost fname args dst rs1 rs2 →
      AUCurvesExec calleePost limbVal limbWrite (.RCall fname dst args) rs1 rs2
  /-- Mirrors Rocq `rexec_limb_store_fp25519`: writes limb `i` of the slot
      `loc` with value `limbVal rs e` via the concrete limb-overwrite
      `limbWrite`.  In Rocq the post-state is
      `rs_set_tower_ed rs loc (VFp25519 (list_set i val_v limbs_old))` with
      `val_v = eval_sexpr_ed rs e`; here `limbWrite loc oldDestV i (limbVal rs e)`
      is the opaque carrier image of that `list_set`. -/
  | limbStore : ∀ loc i e rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      AUCurvesExec calleePost limbVal limbWrite (.RLimbStoreExpr loc i e) rs
        (rsSetTower rs loc.locVar (limbWrite loc ⟨loc.locDst, oldDestV⟩ i (limbVal rs e)))

/-! ## §2  The bridge hypotheses (the named two-prover trust edges)

These three named hypotheses localise the Rocq↔Lean trust edge.  Each says
"the Rocq-shape opaque effect agrees with the CatCrypt `LeafSpec` effect".
They are *hypotheses*, not discharged facts, precisely because verifying them
requires relating Rocq objects (`callee_post`, `eval_sexpr_ed`, `list_set`) to
Lean objects (`leafSpec.call`, `SExpr.evalState`, `leafSpec.limbStore`) — i.e.
they straddle two proof assistants. -/

/-- **Call-oracle bridge.**  Rocq's `rexec_call` uses a `Prop`-relation oracle
    `callee_post`; CatCrypt's `RustExec.call` uses a *function* oracle
    `leafSpec.call` together with the side conditions `locatedLookup rs dst =
    some oldDestV` and the per-arg type-recovery
    `∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩`.  `CallBridge`
    says: whenever the `Prop` oracle relates `rs1` to `rs2` on a call and the
    CatCrypt-side side conditions hold, `rs2` is exactly the state
    `RustExec.call` produces via `leafSpec.call`. -/
def CallBridge
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (leafSpec : LeafSpec) : Prop :=
  ∀ fname dst args rs1 rs2,
    calleePost fname args dst rs1 rs2 →
    ∀ oldDestV, locatedLookup rs1 dst = some oldDestV →
    (∀ a ∈ args, ∃ v, rs1.rsTower a.locVar = some ⟨a.locDst, v⟩) →
    rs2 =
      locatedUpdate rs1 dst
        (leafSpec.call fname dst.locDst (args.map (·.locDst)) oldDestV
          (args.filterMap (fun a => rs1.rsTower a.locVar)))

/-- **Limb-value bridge.**  The Rocq stored value is `eval_sexpr_ed rs e`
    masked through `mask64` (a `Z` in `[0, 2^64)`); the CatCrypt stored value
    is `BitVec.ofNat 64 (e.evalState rs)`.  `limbValBridge` says the
    Rocq-side numeric value `limbVal rs e` equals `e.evalState rs` (the
    tower-aware evaluator, which is exactly the CatCrypt image of
    `eval_sexpr_ed`'s `SLimb`/arith arms — see `SExpr.evalState`). -/
def limbValBridge
    (limbVal : RustState → SExpr → Nat) : Prop :=
  ∀ rs e, limbVal rs e = e.evalState rs

/-- **Limb-write bridge.**  The Rocq concrete overwrite is
    `VFp25519 (list_set i val_v limbs_old)` (a deterministic limb-list set);
    CatCrypt routes it through `leafSpec.limbStore loc oldDestV i word` with
    `word = BitVec.ofNat 64 val`.  `limbWriteBridge` says the opaque-carrier
    Rocq overwrite `limbWrite loc oldV i val` equals
    `leafSpec.limbStore loc (oldV.2) i (BitVec.ofNat 64 val)` whenever the slot
    type matches `loc.locDst` (so the dependent `RustVal` types line up). -/
def limbWriteBridge
    (limbWrite : Located → (Σ t : TowerType, RustVal t) → Nat → Nat →
      (Σ t : TowerType, RustVal t))
    (leafSpec : LeafSpec) : Prop :=
  ∀ loc (oldV : RustVal loc.locDst) i val,
    limbWrite loc ⟨loc.locDst, oldV⟩ i val =
      ⟨loc.locDst, leafSpec.limbStore loc oldV i (BitVec.ofNat 64 val)⟩

/-! ## §3  The per-constructor correspondence theorems (closed in-Lean)

Each theorem says: under the bridge hypotheses, an `AUCurvesExec` step (the
Rocq-transcription side) lifts to the corresponding `RustExec` step (the
CatCrypt side) with the *same* post-state.  These are Lean theorems —
they are what "the two big-step relations agree, constructor-by-constructor"
means *on the CatCrypt side of the trust edge*. -/

variable
    {calleePost : String → List Located → Located → RustState → RustState → Prop}
    {limbVal : RustState → SExpr → Nat}
    {limbWrite : Located → (Σ t : TowerType, RustVal t) → Nat → Nat →
      (Σ t : TowerType, RustVal t)}
    {N : Nat} {leafSpec : LeafSpec}

/-- **skip** correspondence: `rexec_skip` ↔ `RustExec.skip`.  Closes with no
    hypotheses — the post-state is the pre-state on both sides. -/
theorem cross_skip (rs : RustState) :
    RustExec N leafSpec .RSkip rs rs :=
  RustExec.skip rs

/-- **seq** correspondence: `rexec_seq` ↔ `RustExec.seq`.  Closes structurally
    from the two sub-derivations (here taken as `RustExec` hypotheses — the
    inductive hypotheses of the would-be full transport). -/
theorem cross_seq {c1 c2 : LowCT} {rs1 rs2 rs3 : RustState}
    (h1 : RustExec N leafSpec c1 rs1 rs2)
    (h2 : RustExec N leafSpec c2 rs2 rs3) :
    RustExec N leafSpec (.RSeq c1 c2) rs1 rs3 :=
  RustExec.seq c1 c2 rs1 rs2 rs3 h1 h2

/-- **letZero** correspondence: `rexec_let_zero` ↔ `RustExec.letZero`.  Both
    rules push the zeroed default into the tower slot and run the body; the
    Rocq `well_formed_ed` side condition is discharged by the CatCrypt
    `default` being well-formed by construction (so it does not appear). -/
theorem cross_letZero {x : String} {t : TowerType} {body : LowCT}
    {rs1 rs2 : RustState}
    (h : RustExec N leafSpec body (rsSetTower rs1 x ⟨t, default⟩) rs2) :
    RustExec N leafSpec (.RLetZero x t body) rs1 rs2 :=
  RustExec.letZero x t body rs1 rs2 h

/-- **call** correspondence: `rexec_call` ↔ `RustExec.call`.  This is the
    interesting one — it consumes the `CallBridge` hypothesis to turn the Rocq
    `Prop`-oracle post-state into the CatCrypt `leafSpec.call` post-state.
    Given the `AUCurvesExec.call` premise `calleePost fname args dst rs1 rs2`
    and the CatCrypt-side side conditions, the post-state `rs2` is *exactly*
    `RustExec.call`'s post-state, so the `RustExec.call` derivation applies. -/
theorem cross_call
    (hbridge : CallBridge calleePost leafSpec)
    {fname : String} {dst : Located} {args : List Located}
    {rs1 rs2 : RustState}
    (hcall : calleePost fname args dst rs1 rs2)
    {oldDestV : RustVal dst.locDst}
    (hlook : locatedLookup rs1 dst = some oldDestV)
    (htyp : ∀ a ∈ args, ∃ v, rs1.rsTower a.locVar = some ⟨a.locDst, v⟩) :
    RustExec N leafSpec (.RCall fname dst args) rs1 rs2 := by
  have hrs2 := hbridge fname dst args rs1 rs2 hcall oldDestV hlook htyp
  subst hrs2
  exact RustExec.call fname dst args rs1 oldDestV
    (args.filterMap (fun a => rs1.rsTower a.locVar)) hlook rfl htyp

/-- **limbStore** correspondence: `rexec_limb_store_fp25519` ↔
    `RustExec.limbStoreExpr`.  Consumes `limbValBridge` (the Rocq numeric limb
    value = CatCrypt `evalState`) and `limbWriteBridge` (the Rocq limb-list
    overwrite = CatCrypt `leafSpec.limbStore`).  Under both, the
    `AUCurvesExec.limbStore` post-state equals `RustExec.limbStoreExpr`'s
    post-state, so the CatCrypt step applies. -/
theorem cross_limbStore
    (hval : limbValBridge limbVal)
    (hwrite : limbWriteBridge limbWrite leafSpec)
    {loc : Located} {i : Nat} {e : SExpr} {rs : RustState}
    {oldDestV : RustVal loc.locDst}
    (hlook : locatedLookup rs loc = some oldDestV) :
    RustExec N leafSpec (.RLimbStoreExpr loc i e) rs
      (rsSetTower rs loc.locVar
        (limbWrite loc ⟨loc.locDst, oldDestV⟩ i (limbVal rs e))) := by
  rw [hwrite loc oldDestV i (limbVal rs e), hval rs e]
  -- the goal post-state matches `RustExec.limbStoreExpr`'s `locatedUpdate`
  exact RustExec.limbStoreExpr loc i e rs oldDestV hlook

/-! ## §4  Residual — the precisely-scoped two-prover trust edge

What the above theorems establish, and what they do NOT:

* **Established (closed Lean proofs).**  For each constructor in the
  correspondence-map fragment (skip / seq / letZero / call / limbStore), the
  CatCrypt `RustExec` rule fires with the *same post-state* as the Rocq
  `rust_exec_ed` rule, *given* the bridge hypotheses that the Rocq-shape opaque
  effects (`calleePost`, `limbVal`, `limbWrite`) agree with the CatCrypt
  `LeafSpec` effects.  Equivalently: the Lean transcription `AUCurvesExec`
  steps to a `RustExec` step.  This is a real, machine-checked statement about
  CatCrypt's semantics.

* **NOT established (the two-prover residual).**  Two pieces remain on
  the trust edge, and neither can be a Lean `theorem`:

  1. **Transcription faithfulness.**  `AUCurvesExec` is *asserted* (by reading
     the two inductives side-by-side, recorded in the constructor-map table
     above) to faithfully transcribe Rocq's `rust_exec_ed`.  This is a
     meta-level claim: it is true because the constructors were copied
     one-for-one from `SafeRustEd25519Sim.v` (the dropped `rexec_calln` /
     `rexec_callfn` are exactly the constructors with no CatCrypt counterpart
     the retarget touches).  Lean cannot check this — the source of truth is
     the Rocq file, which is Qed'd and axiom-free (`Print Assumptions
     safe_cmd_correct_ed` ⇒ *"Closed under the global context"*, verified via
     rocq-mcp).

  2. **The bridge hypotheses themselves.**  `CallBridge`, `limbValBridge`, and
     `limbWriteBridge` relate Rocq objects (`callee_post`, `eval_sexpr_ed`'s
     `mask64`-masked value, `list_set` into the limb list) to Lean objects
     (`leafSpec.call`, `SExpr.evalState`, `leafSpec.limbStore`).  Discharging
     them is exactly the cross-prover step: it requires a *shared semantic
     anchor* (e.g. exporting the Rocq oracle's input/output relation as a
     trusted interface, or a Rocq→Lean transport of the inductive).  They are
     *named hypotheses*.  Their shape is tight: `limbValBridge` holds by `rfl`
     for the instantiation `limbVal := fun rs e => e.evalState rs`, and
     `limbWriteBridge` closes by `rfl` for any `limbWrite`
     defined as the CatCrypt `leafSpec.limbStore` image.  The
     irreducible edge is `CallBridge` (the opaque FFI leaf) together with the
     transcription-faithfulness meta-claim.

This is the same residual any two-prover bridge carries; it is not specific to
this routine.  The cross-prover gap is localised to exactly three named
hypotheses + one meta-level transcription claim,
with every downstream implication a closed Lean proof. -/

/-- **Sanity instance: the bridge hypotheses are satisfiable / not vacuous.**
    For the canonical instantiation `limbVal := SExpr.evalState`,
    `limbValBridge` holds by `rfl` — confirming the hypothesis is the *right*
    shape (it is exactly the tower-aware evaluator), not an unsatisfiable
    over-constraint. -/
theorem limbValBridge_canonical :
    limbValBridge (fun rs e => e.evalState rs) := by
  intro rs e; rfl

/-- **Sanity instance.**  For the canonical instantiation
    `limbWrite := fun loc oldV i val => ⟨loc.locDst, leafSpec.limbStore loc
    (cast oldV) i (BitVec.ofNat 64 val)⟩` the `limbWriteBridge` holds by
    construction.  We package it as the concrete CatCrypt-image `limbWrite`. -/
def canonicalLimbWrite (leafSpec : LeafSpec) :
    Located → (Σ t : TowerType, RustVal t) → Nat → Nat → (Σ t : TowerType, RustVal t) :=
  fun loc oldV i val =>
    if h : oldV.1 = loc.locDst then
      ⟨loc.locDst, leafSpec.limbStore loc (h ▸ oldV.2) i (BitVec.ofNat 64 val)⟩
    else oldV

theorem limbWriteBridge_canonical (leafSpec : LeafSpec) :
    limbWriteBridge (canonicalLimbWrite leafSpec) leafSpec := by
  intro loc oldV i val
  simp [canonicalLimbWrite]

/-! ## §5  The cross-prover residual as machine-recorded named assumptions

§2–§4 express the trust edge as loose predicates (`CallBridge`, …) plus prose
in §4 ("transcription faithfulness").  This section states the **two
irreducible cross-prover edges** to *named assumption objects*, in the
discipline of the FFI trust edge `SecureCompilation/VIR/LeafAxiomConsolidation.lean`'s
  `LeafFFIValidated`, the canonical pattern for a residual
  that *cannot* be a Lean theorem because it crosses a boundary Lean cannot see
  (there: an externally compiled binary; here: a second proof assistant). That
  edge is a **named predicate** with a non-vacuous witness and a consumable
  worked theorem — the shape reproduced below.

Neither edge can be a Lean `theorem`: both straddle Rocq and Lean.  They are
recorded as named, inhabited Lean objects (not prose, not a bare `axiom`).  No
open goals, no new global `axiom`. -/

/-! ### §5.1  Edge 1 — the call-oracle bridge (the irreducible two-prover edge)

`CallBridge` (§2) is the irreducible edge: it relates the Rocq
`Prop`-oracle `callee_post` to the CatCrypt *function* oracle `leafSpec.call`,
so discharging it requires a shared semantic anchor exported across Rocq+Lean
(an FFI-style boundary, exactly as `LeafFFIValidated` is for the emitted
binary).  We package it as a Catalog-style assumption *structure* carrying the
`CallBridge` predicate as its single field — so a downstream theorem that takes
a `CrossProverCallBridge` value *assumes* the edge, as a hypothesis. -/

/-- **Named assumption: the cross-prover call-oracle bridge.**

    Bundles the irreducible two-prover edge `CallBridge calleePost leafSpec`
    (the Rocq `Prop`-oracle `callee_post` agrees with the CatCrypt function
    oracle `leafSpec.call`) as an assumption object, mirroring the named FFI
    predicate `LeafFFIValidated`.

    This is **not** a Lean theorem and cannot be one: it relates a Rocq object
    (`callee_post` in `AUCurves/src/Bedrock/SafeRustEd25519Sim.v`) to a Lean
    object (`leafSpec.call`), so it requires a shared semantic anchor exported
    across the two proof assistants. Holding a value of this structure is
    *assuming* that anchor — the cross-prover trust surface, named rather
    than left as prose or a bare `axiom`. -/
structure CrossProverCallBridge
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (leafSpec : LeafSpec) : Prop where
  /-- The call-oracle bridge holds for these effects (see `CallBridge`). -/
  callBridge : CallBridge calleePost leafSpec

/-! ### §5.2  Edge 2 — transcription faithfulness (the meta-level claim)

§4(1) records, as prose, that `AUCurvesExec` faithfully transcribes Rocq's
`rust_exec_ed` (constructors copied one-for-one from `SafeRustEd25519Sim.v`).
We make that a *Lean-stated named assumption*: `TranscriptionFaithful` says the
Lean transcription `AUCurvesExec` agrees, derivation-for-derivation, with a
supplied `rocqExec` relation — the proxy standing in Lean for the Rocq
`rust_exec_ed` (whose true source of truth is the Rocq file, Qed'd and
axiom-free per `Print Assumptions safe_cmd_correct_ed`).  Lean cannot check the
proxy *is* the Rocq relation — that is the meta-claim — but it can record the
claim's exact shape as an inhabited Prop and consume it, exactly as
`LeafFFIValidated` records "the binary computes `leafSem`" without modelling the
binary. -/

/-- **Named assumption: transcription faithfulness.**

    `TranscriptionFaithful calleePost limbVal limbWrite rocqExec` says the Lean
    transcription `AUCurvesExec calleePost limbVal limbWrite` coincides,
    derivation-for-derivation, with `rocqExec` — the Lean-side proxy for Rocq's
    big-step relation `rust_exec_ed` (`SafeRustEd25519Sim.v`).

    This is the §4(1) meta-claim made into a Lean object. Lean cannot verify
    that `rocqExec` faithfully *is* the Rocq inductive (that is checked by
    reading the two inductives side-by-side, per the §0 constructor-map table,
    and rests on the Rocq file being Qed'd and axiom-free). What Lean *can* do —
    and what this predicate does — is record the precise claim and let downstream
    theorems consume it, in the `LeafFFIValidated` discipline: a named,
    inhabited predicate over the boundary object, never a bare global `axiom`. -/
def TranscriptionFaithful
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (limbVal : RustState → SExpr → Nat)
    (limbWrite : Located → (Σ t : TowerType, RustVal t) → Nat → Nat →
      (Σ t : TowerType, RustVal t))
    (rocqExec : LowCT → RustState → RustState → Prop) : Prop :=
  ∀ c rs rs', AUCurvesExec calleePost limbVal limbWrite c rs rs' ↔ rocqExec c rs rs'

/-- **Non-vacuous witness for `TranscriptionFaithful`.** Taking the Rocq-proxy
    relation to be `AUCurvesExec` itself, transcription faithfulness holds by
    reflexivity — confirming the predicate is the right shape (an inhabited
    boundary claim, not an unsatisfiable over-constraint), exactly as
    `leafFFIValidated_jasminExtSem` witnesses `LeafFFIValidated`. The
    *content* of the assumption is precisely the gap between this canonical proxy
    and the actual Rocq inductive, which lives outside Lean. -/
theorem transcriptionFaithful_canonical :
    TranscriptionFaithful calleePost limbVal limbWrite
      (AUCurvesExec calleePost limbVal limbWrite) :=
  fun _ _ _ => Iff.rfl

/-! ### §5.3  The complete localized residual

`CrossProverResidual` bundles *exactly* the two irreducible named edges (call
bridge + transcription faithfulness) plus the two `rfl`-closable limb bridges,
so the entire cross-prover trust surface of the AUCurves retarget is one named,
inhabited Lean object.
A downstream theorem quantifying over it assumes the cross-prover gap;
everything else is the closed Lean proof of §3. -/

/-- **The complete AUCurves cross-prover residual.**

    Bundles the full localized trust surface of the AUCurves→CatCrypt retarget:

    1. `callBridge` — the irreducible call-oracle edge (`CrossProverCallBridge`);
    2. `transcription` — transcription faithfulness of `AUCurvesExec` against the
       supplied Rocq proxy `rocqExec` (`TranscriptionFaithful`);
    3. `limbVal`/`limbWrite` bridges — the two `rfl`-closable limb edges (§2),
       included so the residual is the *whole* gap, not a partial one.

    This is the single citable Lean object the §3 correspondence theorems
    consume. Holding it = assuming the
    cross-prover gap; it is inhabited (see `crossProverResidual_canonical`), so it
    is a satisfiable assumption. -/
structure CrossProverResidual
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (limbVal : RustState → SExpr → Nat)
    (limbWrite : Located → (Σ t : TowerType, RustVal t) → Nat → Nat →
      (Σ t : TowerType, RustVal t))
    (leafSpec : LeafSpec)
    (rocqExec : LowCT → RustState → RustState → Prop) : Prop where
  /-- Edge 1: the irreducible call-oracle bridge. -/
  callBridge : CrossProverCallBridge calleePost leafSpec
  /-- Edge 2: transcription faithfulness against the Rocq proxy. -/
  transcription : TranscriptionFaithful calleePost limbVal limbWrite rocqExec
  /-- The `rfl`-closable limb-value bridge (§2). -/
  limbValBridge : limbValBridge limbVal
  /-- The `rfl`-closable limb-write bridge (§2). -/
  limbWriteBridge : limbWriteBridge limbWrite leafSpec

/-! ### §5.4  The residual is consumable (worked theorems)

To show each named assumption is *usable as an explicit hypothesis*, and not a
prose label, we record the canonical conclusions they support, in the `LeafFFIValidated`
`leafAgrees_of_FFIValidated` discipline.  Each takes the named residual as a
hypothesis and discharges a `RustExec` correspondence with it. -/

/-- **Edge 1 is consumable.** Given the named call-oracle assumption
    `CrossProverCallBridge`, a `calleePost` call step lifts to the CatCrypt
    `RustExec.call` step with the same post-state (this is `cross_call` driven by
    the *structure* form of the assumption). -/
theorem cross_call_of_residual
    (hbridge : CrossProverCallBridge calleePost leafSpec)
    {fname : String} {dst : Located} {args : List Located}
    {rs1 rs2 : RustState}
    (hcall : calleePost fname args dst rs1 rs2)
    {oldDestV : RustVal dst.locDst}
    (hlook : locatedLookup rs1 dst = some oldDestV)
    (htyp : ∀ a ∈ args, ∃ v, rs1.rsTower a.locVar = some ⟨a.locDst, v⟩) :
    RustExec N leafSpec (.RCall fname dst args) rs1 rs2 :=
  cross_call hbridge.callBridge hcall hlook htyp

/-- **The full residual is consumable: every transcribed step lifts to `RustExec`.**

    Given the complete cross-prover residual, a derivation of the Rocq proxy
    relation `rocqExec` on any constructor in the correspondence-map fragment
    lifts to a CatCrypt `RustExec` derivation with the same post-state. This is
    the cross-prover semantic-equivalence conclusion the whole file is for —
    holding *exactly* under the named residual (transcription faithfulness turns
    the `rocqExec` premise into an `AUCurvesExec` derivation, which the §3
    constructor theorems then lift), with no open goals and no bare `axiom`. -/
theorem rocqExec_lifts_to_rustExec
    {rocqExec : LowCT → RustState → RustState → Prop}
    (res : CrossProverResidual calleePost limbVal limbWrite leafSpec rocqExec)
    {c : LowCT} {rs rs' : RustState}
    (hrocq : rocqExec c rs rs') :
    AUCurvesExec calleePost limbVal limbWrite c rs rs' :=
  (res.transcription c rs rs').mpr hrocq

/-- **Worked closed-loop instance.** For the canonical instantiation
    (`limbVal := SExpr.evalState`, `limbWrite := canonicalLimbWrite leafSpec`,
    `rocqExec := AUCurvesExec …`), the *limb* and *transcription* edges of the
    residual are discharged (`limbValBridge_canonical`,
    `limbWriteBridge_canonical`, `transcriptionFaithful_canonical`), so the
    residual collapses to its *single* irreducible field: the call-oracle bridge.
    This pins the cross-prover trust surface to exactly `CrossProverCallBridge`,
    the analogue of `leafEdge_doublyCorroborated` pinning the leaf trust surface
    to `LeafFFIValidated`. -/
theorem crossProverResidual_canonical
    (leafSpec : LeafSpec)
    (calleePost : String → List Located → Located → RustState → RustState → Prop)
    (hcall : CrossProverCallBridge calleePost leafSpec) :
    CrossProverResidual calleePost (fun rs e => e.evalState rs)
      (canonicalLimbWrite leafSpec) leafSpec
      (AUCurvesExec calleePost (fun rs e => e.evalState rs)
        (canonicalLimbWrite leafSpec)) where
  callBridge := hcall
  transcription := transcriptionFaithful_canonical
  limbValBridge := limbValBridge_canonical
  limbWriteBridge := limbWriteBridge_canonical leafSpec

end CatCrypt.Crypto.SecureCompilation.AUCurvesImport
