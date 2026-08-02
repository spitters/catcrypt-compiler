/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# POC: a non-optimizing verified lowering of a Rust subset to LowCT (`LowCT`)

**Status: proof-of-concept (#270, first step).** This module establishes the
*skeleton* of a faithful, non-optimizing verified lowering from a restricted
Rust subset to LowCT (= the `LowCT` IR of
`CatCrypt/Crypto/Jasmin/LowCT.lean`), and proves the lowering correct for
**one representative source program** via a relational-compilation relation in
the style of the SHA-2 / Keccak Rupicola layer
(`CatCrypt/Crypto/SecureCompilation/RelationalCompile.lean`). It is **not** the
full lowering; §"Scope report" below states what the full thing needs.

## What this connects (the security-front / perf-front seam)

CatCrypt currently bridges hax-extracted Rust to the compiled (Jasmin/asm)
artifact via a *per-protocol* `LeafAgrees` / `FrontValueAgrees` hypothesis: an
*assumed* agreement between the abstract spec's leaf and the compiled leaf. A
verified `Rust-subset → LowCT` lowering replaces that assumption, *for the code
it covers*, with a proved fact: the LowCT program the back-end compiles is the
denotational image of the very same Rust the UC spec reads. The same Rust
artifact becomes both the UC spec source and the compiled source, joined by a
proved lowering — closing the seam for cold/glue code.

## §0  Subset representation chosen — and why

The **canonical Rust frontend** is hax's typed AST `CatCrypt.Hax.ImpExpr`
(`CatCrypt/Hax/AST.lean`): an expression-oriented Rust subset with `letBind`,
`app`, `ifThenElse`, `forFold`, `assign`, fixed-width scalar literals, and
tuples. We do **not** re-parse Rust — that frontend is the trusted reader.

`ImpExpr`, however, is *value-oriented* (every node returns a `Value`), whereas
LowCT (`LowCT`) is *statement-oriented over a mutable `RustState`* whose
scalar slots are `u64` (`rsScalar : String → Nat`). The faithful object to lower
is therefore the **statement-level desugaring** of `ImpExpr`, not `ImpExpr`
directly. For this POC we make that desugared form *explicit* as a small subset
datatype `RustSrc` below, and document the (out-of-scope, mechanical) map
`ImpExpr → RustSrc`. We pick the **explicit subset datatype** (rather than
lowering `ImpExpr` wholesale) for two reasons:

1. **Self-contained semantics.** The scalar fragment of `RustExec`
   (`scalarSetExpr`, `forSucc`/`forZero`, `ifTrue`/`ifFalse`, `letU64Zero`,
   `seq`, `skip`) is closed under `rsScalar` alone — it has **no `LeafSpec`
   dependence** — so we get a total, provable end-to-end semantics for the POC
   without dragging in the tower-value / leaf-oracle machinery. The full
   lowering (scope report) extends to the tower/array constructors, which *do*
   touch the oracle.
2. **1:1-ish faithfulness is visible.** A bespoke statement datatype makes the
   "one source constructor → one `LowCT` constructor" non-optimizing
   discipline (no instruction selection, no register allocation, no
   vectorization) syntactically obvious and auditable.

The subset covers: `let x = e`, scalar assignment `x = e`, `if c { … } else { … }`,
bounded `for x in 0..n { … }` (const range), sequencing, and
arithmetic/bitwise operators — all over the `SExpr` scalar-expression language
`LowCT` already provides (`SVar/SLit/SAdd/SMul/SShr/SShl/SAnd/SXor/…`),
satisfying the **ANF / flat-RHS** requirement: every assignment RHS is a single
`SExpr`, so the asmgen-rejected nested-arithmetic form never arises (the `SExpr`
tree is the flat right-hand side; nested `SExpr` nodes are scalar temporaries
the back-end flattens, not nested *statements*).

Fixed-size arrays and `u32`/`u64` width tracking are present in `LowCT`
(`TArr`, `RArrStore`/`RArrStoreLit`, `TU32`/`TU64`) and called out in the scope
report; the POC's representative program exercises the scalar core, which is
where the correctness *method* is established.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.RustSubsetToLowCT

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The Rust subset source language `RustSrc`

`RustSrc` is the explicit statement-level desugaring of the scalar fragment of
hax's `ImpExpr`. Each constructor maps to exactly one `LowCT` statement (the
non-optimizing discipline), and its semantics `RustSrc.exec` is a direct
state-transformer over the scalar environment `σ : String → Nat` — the same
model `RustExec` uses for `rsScalar`. -/

/-- The Rust subset: scalar `let`, assignment, `if`, bounded `for`, sequencing,
    skip. RHS expressions are `SExpr` (the flat scalar expression language of
    `LowCT`). -/
inductive RustSrc where
  /-- `;`-sequencing of two statements. -/
  | seq    : RustSrc → RustSrc → RustSrc
  /-- the empty statement. -/
  | skip   : RustSrc
  /-- `let x = e;` — introduce a fresh `u64` scalar binding initialised to `e`.
      (Desugars `ImpExpr.letBind name (scalar val) body`.) -/
  | letE   : String → SExpr → RustSrc → RustSrc
  /-- `x = e;` — scalar assignment. (Desugars `ImpExpr.assign name (scalar rhs)`.) -/
  | assign : String → SExpr → RustSrc
  /-- `if c != 0 { thn } else { els }`. The guard is an `SExpr`; the subset
      tests "non-zero" (the `RIfNz` shape). (Desugars `ImpExpr.ifThenElse`.) -/
  | ifNz   : SExpr → RustSrc → RustSrc → RustSrc
  /-- `for x in 0..n { body }` — `n` a compile-time `Nat`. On iteration `i`,
      `x` is bound to `i`. (Desugars `ImpExpr.forFold var 0 n body`.) -/
  | forN   : String → Nat → RustSrc → RustSrc
  deriving Repr, Inhabited

/-- Source-level semantics: a state-transformer over the scalar environment
    `σ : String → Nat`. This is the *spec* the lowering must realize, phrased on
    the very same `rsScalar`-style map `RustExec` threads, so the
    correctness theorem can compare the two directly.

    * `seq`   — run then run.
    * `letE`  — bind `x := eval e`, run body. (A `u64` scalar binding is just a
      `rsScalar` write in this model; scope-exit is a no-op at the scalar level,
      matching `RustExec.letU64Zero` followed by the body.)
    * `assign`— `x := eval e`.
    * `ifNz`  — branch on `eval c ≠ 0`.
    * `forN`  — `Nat.rec`: 0 iters = identity; `n+1` iters = run `n` then set
      `x := n` and run body. This is *exactly* `RustExec.forSucc`'s shape. -/
def RustSrc.exec : RustSrc → (String → Nat) → (String → Nat)
  | .seq c1 c2, σ => c2.exec (c1.exec σ)
  | .skip,      σ => σ
  | .letE x e body, σ =>
      body.exec (fun y => if y = x then e.eval σ else σ y)
  | .assign x e, σ => fun y => if y = x then e.eval σ else σ y
  | .ifNz c thn els, σ =>
      if c.eval σ ≠ 0 then thn.exec σ else els.exec σ
  | .forN x n body, σ =>
      Nat.rec σ
        (fun i acc => body.exec (fun y => if y = x then i else acc y)) n

/-! ### A note on the scalar-write model

`RustExec` writes scalars via `rsSetScalar rs x v = { rs with rsScalar := fun y
=> if y == x then v else rs.rsScalar y }`. `RustSrc.exec` uses the
*propositional* `if y = x` (decidable on `String`) rather than the `==` `Bool`
form; they agree pointwise (`beq_iff_eq`). The bridge lemma `scalarUpdate_eq`
below records this so the lowering proof reads the two updates as equal. -/

/-- The `RustExec` scalar update (`==`) equals the `RustSrc.exec` update (`=`). -/
theorem scalarUpdate_eq (σ : String → Nat) (x : String) (v : Nat) :
    (fun y => if y == x then v else σ y) = (fun y => if y = x then v else σ y) := by
  funext y
  by_cases h : y = x <;> simp [h]

/-! ## §2  The non-optimizing lowering `lower : RustSrc → LowCT`

One source constructor → one `LowCT` statement. No instruction selection, no
register allocation, no vectorization, no reassociation. The `SExpr` RHS is
passed through verbatim (it is already the flat right-hand side), so this is the
ANF/flat-RHS-respecting 1:1 lowering.

| `RustSrc`            | `LowCT`                              |
|----------------------|----------------------------------------|
| `seq c1 c2`          | `RSeq (lower c1) (lower c2)`           |
| `skip`               | `RSkip`                                |
| `letE x e body`      | `RSeq (RScalarSetExpr x e) (lower body)` |
| `assign x e`         | `RScalarSetExpr x e`                   |
| `ifNz c thn els`     | guard temp `+` `RIfNz` over the two arms |
| `forN x n body`      | `RFor x n (lower body)`                |

For `letE` we lower a scalar `let` to a plain `RScalarSetExpr` write (no
`RLetU64Zero` scope-zeroing wrapper). The reason is **faithfulness**:
`RLetU64Zero x` zeroes `x` *before* the RHS is evaluated, so wrapping the RHS in
it would make `let x = e` see `x = 0` inside `e` — wrong when `e` reads a prior
`x` (Rust shadowing evaluates the RHS in the *outer* scope). `RScalarSetExpr x e`
evaluates `e` in the current environment then writes `x`, matching the source
semantics exactly. The `RLetU64Zero` scope marker is only meaningful for stack
reuse at the *byte* level (a back-end concern); at the scalar-denotation level a
`let` is a write, and emitting the scope marker would require a separate
RHS-temporary to stay faithful (a full-lowering refinement, scope report).

For `ifNz` the guard is an `SExpr`, but `RIfNz` branches on a *scalar slot*
(`rs.rsScalar e`). The non-optimizing lowering therefore materialises the guard
into a fresh slot first: `RScalarSetExpr g c ; RIfNz g (lower thn) (lower els)`.
This is the faithful, minimal expansion (a guard is evaluated to a temporary,
then branched on) — still 1:1-ish (one extra binding per `if`, no optimization).
-/

/-- Fresh guard-slot name for an `if`. In the POC we use a fixed reserved name;
    a full lowering threads a gensym counter (scope report). The representative
    program below has no `if`, so the choice is immaterial to the proved case;
    the arm is included for completeness of the skeleton. -/
def guardSlot : String := "__lowct_guard"

/-- The non-optimizing lowering. -/
def lower : RustSrc → LowCT
  | .seq c1 c2 => .RSeq (lower c1) (lower c2)
  | .skip => .RSkip
  | .letE x e body => .RSeq (.RScalarSetExpr x e) (lower body)
  | .assign x e => .RScalarSetExpr x e
  | .ifNz c thn els =>
      .RSeq (.RScalarSetExpr guardSlot c)
        (.RIfNz guardSlot (lower thn) (lower els))
  | .forN x n body => .RFor x n (lower body)

/-! ## §3  The relational-compilation relation `RRefines` (LowCT analogue)

`RRefines spec c` is the LowCT counterpart of `RelationalCompile.Refines`: it
says the lowered command `c`, run under `RustExec`, advances the scalar state by
`spec` — *for every* fuel bound `N` and leaf spec (the scalar fragment is
independent of both). It is **denotational** in the same sense: a fragment
refines a state-step when running it relates the pre/post scalar maps by `spec`.

This is deliberately the *same architecture* as the VIR-emitter `Refines`
(§1–§3 of `RelationalCompile.lean`): atomic compilation lemmas, a `seq`
composition rule, an identity/`skip` base case, a bounded-loop rule, and cons
forms — so a lowering-correctness proof is *assembled* from reusable lemmas, not
written as a bespoke `RustExec` induction per program. The §4 representative
proof is discharged by a `rupicola_rust` driver built from these. -/

/-- `RRefines spec c`: under any fuel `N` and leaf spec, running the *lowered*
    command `c` from any state `rs` whose scalar map is `σ` lands in a state
    whose scalar map is `spec σ` (and the tower heap is irrelevant — the scalar
    fragment never reads or writes it). Concretely: there is an output state
    reachable by `RustExec`, and every reachable output state has scalar map
    `spec σ`.

    We phrase the existence side as "for the canonical scalar-only run there is
    a derivation" and the uniqueness side as the scalar-map equation; together
    they say the lowered command *denotes* `spec`. -/
def RRefines (spec : (String → Nat) → (String → Nat)) (c : LowCT) : Prop :=
  ∀ (N : Nat) (leafSpec : LeafSpec) (rs : RustState),
    ∃ rs', CatCrypt.Crypto.Jasmin.LowCT.RustExec N leafSpec c rs rs' ∧
      rs'.rsScalar = spec rs.rsScalar

open CatCrypt.Crypto.Jasmin.LowCT (RustExec rsSetScalar)

/-! ### §3.1  Atomic compilation lemmas -/

/-- **Skip compilation lemma.** `RSkip` refines the identity step. -/
theorem RRefines.skip : RRefines (fun σ => σ) .RSkip := by
  intro N leafSpec rs
  exact ⟨rs, RustExec.skip rs, rfl⟩

/-- **Assignment compilation lemma.** `RScalarSetExpr x e` refines the scalar
    write `σ ↦ σ[x := eval e σ]`. -/
theorem RRefines.assign (x : String) (e : SExpr) :
    RRefines (fun σ => fun y => if y = x then e.eval σ else σ y)
      (.RScalarSetExpr x e) := by
  intro N leafSpec rs
  refine ⟨_, RustExec.scalarSetExpr x e rs, ?_⟩
  simp only [rsSetScalar]
  exact scalarUpdate_eq rs.rsScalar x (e.eval rs.rsScalar)

/-- **Sequencing compilation lemma** — the composition rule. If `c1` refines
    `spec1` and `c2` refines `spec2`, then `RSeq c1 c2` refines `spec2 ∘ spec1`.
    The post-state of `c1` is fed to `c2`; because `RRefines` quantifies over all
    starting states, `c2`'s refinement applies at `c1`'s output. -/
theorem RRefines.seq {spec1 spec2 : (String → Nat) → (String → Nat)}
    {c1 c2 : LowCT} (h1 : RRefines spec1 c1) (h2 : RRefines spec2 c2) :
    RRefines (fun σ => spec2 (spec1 σ)) (.RSeq c1 c2) := by
  intro N leafSpec rs
  obtain ⟨rs1, hex1, hsc1⟩ := h1 N leafSpec rs
  obtain ⟨rs2, hex2, hsc2⟩ := h2 N leafSpec rs1
  refine ⟨rs2, RustExec.seq c1 c2 rs rs1 rs2 hex1 hex2, ?_⟩
  rw [hsc2, hsc1]

/-- **`let`-binding compilation lemma.** `RLetU64Zero x body'` introduces a
    zero-initialised scalar slot `x`, then runs `body'`. At the scalar level the
    zero-init is a `rsSetScalar rs x 0`; the body then overwrites it (in our
    `lower`, with `RScalarSetExpr x e`). The lemma says: if `body'` refines
    `specBody` *starting from the state with `x := 0`*, then `RLetU64Zero x
    body'` refines `σ ↦ specBody (σ[x := 0])`. -/
theorem RRefines.letU64Zero (x : String) {specBody : (String → Nat) → (String → Nat)}
    {body' : LowCT} (hbody : RRefines specBody body') :
    RRefines (fun σ => specBody (fun y => if y = x then 0 else σ y))
      (.RLetU64Zero x body') := by
  intro N leafSpec rs
  obtain ⟨rs', hex, hsc⟩ := hbody N leafSpec (rsSetScalar rs x 0)
  refine ⟨rs', RustExec.letU64Zero x body' rs rs' hex, ?_⟩
  rw [hsc]
  simp only [rsSetScalar]
  rw [scalarUpdate_eq]

/-! ### §3.2  Bounded-loop compilation lemma (`RFor`)

The LowCT counterpart of `RelationalCompile.Refines.forUnrolled`. `RFor x n
body'` runs `body'` `n` times with `x` bound to the iteration index. If `body'`
refines a per-iteration step `bodyStep`, the loop refines the `Nat.rec` fold of
the per-iteration "set `x := i`, then `bodyStep`" step. -/

/-- The spec-level fold of a per-iteration body step over `0..n`, with the loop
    counter `x` set to `i` on iteration `i`. Mirrors `RustExec.forSucc`. -/
def forStepFold (x : String) (bodyStep : (String → Nat) → (String → Nat)) :
    Nat → (String → Nat) → (String → Nat)
  | 0,      σ => σ
  | (n+1),  σ => bodyStep (fun y => if y = x then n else (forStepFold x bodyStep n σ) y)

/-- `forStepFold` with the body step instantiated at `body.exec` is exactly the
    source semantics of `forN x n body` — both are the same `Nat.rec` over the
    counter-binding step. -/
theorem forStepFold_exec (x : String) (body : RustSrc) (n : Nat) (σ : String → Nat) :
    forStepFold x (RustSrc.exec body) n σ = RustSrc.exec (.forN x n body) σ := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [forStepFold, RustSrc.exec] at *; rw [ih]

/-- **Bounded-loop compilation lemma.** If `body'` refines `bodyStep`, then
    `RFor x n body'` refines `forStepFold x bodyStep n`. Proven by induction on
    `n`, one `RustExec.forSucc` per unrolling — i.e. the loop lemma is assembled
    from the same `RustExec` structural steps, not a bespoke fixpoint argument. -/
theorem RRefines.forN (x : String) {bodyStep : (String → Nat) → (String → Nat)}
    {body' : LowCT} (hbody : RRefines bodyStep body') :
    ∀ (n : Nat), RRefines (forStepFold x bodyStep n) (.RFor x n body') := by
  intro n
  induction n with
  | zero =>
    intro N leafSpec rs
    exact ⟨rs, RustExec.forZero x body' rs, rfl⟩
  | succ k ih =>
    intro N leafSpec rs
    obtain ⟨rs1, hex1, hsc1⟩ := ih N leafSpec rs
    obtain ⟨rs2, hex2, hsc2⟩ := hbody N leafSpec (rsSetScalar rs1 x k)
    refine ⟨rs2, RustExec.forSucc x k body' rs rs1 rs2 hex1 hex2, ?_⟩
    rw [hsc2]
    simp only [forStepFold, rsSetScalar]
    rw [hsc1, scalarUpdate_eq]

/-! ### §3.3  The `if`-free fragment: full structural lowering correctness

`lowerRefines` connects §2's `lower` to §3's relation for the **`if`-free
fragment** of the subset (`skip`, `assign`, `seq`, `letE`, `forN`): it proves
`RRefines (RustSrc.exec src) (lower src)` by assembling the atomic / `seq` /
`let` / loop compilation lemmas along the syntax. This is the LowCT analogue of
the `rupicola` driver — the subset's first-order syntax lets a plain structural
recursion drive the same compilation lemmas (no CPS-continuation elaborator
needed).

The `ifNz` arm is handled by a separate compilation lemma `RRefines.ifNz`
(§3.4) carrying its honest side condition (guard-slot freshness); see the scope
report for why the recursive driver excludes it. The representative program
(§4) lives in this `if`-free fragment, which is precisely the
straight-line-arithmetic + bounded-loop fragment the POC targets. -/

/-- `true` iff `src` is in the `if`-free fragment (`skip/assign/seq/letE/forN`).
    The structural lowering theorem below is proven for this fragment. -/
def RustSrc.ifFree : RustSrc → Bool
  | .skip => true
  | .assign _ _ => true
  | .seq c1 c2 => c1.ifFree && c2.ifFree
  | .letE _ _ body => body.ifFree
  | .forN _ _ body => body.ifFree
  | .ifNz _ _ _ => false

/-- The lowering of an `if`-free source program refines its source semantics.
    Assembled entirely from the §3.1–§3.2 compilation lemmas. -/
theorem lowerRefines : ∀ (src : RustSrc), src.ifFree = true →
    RRefines (RustSrc.exec src) (lower src)
  | .skip, _ => by
      simpa [lower, RustSrc.exec] using RRefines.skip
  | .assign x e, _ => by
      simpa [lower, RustSrc.exec] using RRefines.assign x e
  | .seq c1 c2, h => by
      simp only [RustSrc.ifFree, Bool.and_eq_true] at h
      have := RRefines.seq (lowerRefines c1 h.1) (lowerRefines c2 h.2)
      simpa [lower, RustSrc.exec] using this
  | .letE x e body, h => by
      simp only [RustSrc.ifFree] at h
      -- lower = RSeq (RScalarSetExpr x e) (lower body); same shape as the spec
      -- `body.exec ∘ (σ ↦ σ[x := eval e σ])`. Assemble from assign + seq.
      have := RRefines.seq (RRefines.assign x e) (lowerRefines body h)
      simpa [lower, RustSrc.exec] using this
  | .forN x n body, h => by
      simp only [RustSrc.ifFree] at h
      -- lower = RFor x n (lower body); spec = forStepFold x (body.exec) n.
      have hloop := RRefines.forN x (lowerRefines body h) n
      refine fun N leafSpec rs => ?_
      obtain ⟨rs', hex, hsc⟩ := hloop N leafSpec rs
      refine ⟨rs', hex, ?_⟩
      rw [hsc, forStepFold_exec]

/-! ### §3.4  The `if` compilation lemma (with its honest guard-write spec)

The `ifNz` lowering materialises the guard into a fresh slot
(`RScalarSetExpr guardSlot c ; RIfNz guardSlot …`), then branches on that slot.
The lowering really does **clobber** `guardSlot` (it is a materialised
temporary), so the *honest* refinement spec pre-composes the branch step with
the guard write `σ ↦ σ[guardSlot := c.eval σ]` — we carry that explicitly in the
conclusion rather than pretending the temporary is invisible.

The **residual** for the full lowering is to make `guardSlot` *fresh* (a gensym
not read/written by either branch) and then **frame it out** of the observable
post-state, recovering the clean `if c then specThn else specEls` spec. That is
the LowCT analogue of the VIR emitter's slot-disjointness side conditions (which
live, proved-once, inside `Refines.arith`); see the scope report. -/

/-- **`if` compilation lemma.** Given branch refinements, the guard-materialising
    `if` lowering refines the branching step **pre-composed with the guard write**
    `σ ↦ σ[guardSlot := c.eval σ]`. Proved outright (no freshness hypothesis): the
    guard write is reflected in the conclusion, so the lemma is exact. Framing the
    guard slot out of the observable spec is the residual (scope report). -/
theorem RRefines.ifNz (c : SExpr) {specThn specEls : (String → Nat) → (String → Nat)}
    {thn' els' : LowCT}
    (hThn : RRefines specThn thn') (hEls : RRefines specEls els') :
    RRefines
      (fun σ =>
        let σg := fun y => if y = guardSlot then c.eval σ else σ y
        if c.eval σ ≠ 0 then specThn σg else specEls σg)
      (.RSeq (.RScalarSetExpr guardSlot c)
        (.RIfNz guardSlot thn' els')) := by
  intro N leafSpec rs
  obtain ⟨rsg, hexg, hscg⟩ := RRefines.assign guardSlot c N leafSpec rs
  have hguard : rsg.rsScalar guardSlot = c.eval rs.rsScalar := by
    rw [hscg]; simp
  have hgσ : rsg.rsScalar = fun y => if y = guardSlot then c.eval rs.rsScalar else rs.rsScalar y :=
    hscg
  by_cases hc : c.eval rs.rsScalar = 0
  · obtain ⟨rs', hex', hsc'⟩ := hEls N leafSpec rsg
    refine ⟨rs', RustExec.seq _ _ rs rsg rs' hexg
      (RustExec.ifFalse guardSlot thn' els' rsg rs' (by rw [hguard, hc]) hex'), ?_⟩
    rw [hsc', hgσ]
    simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte]
  · obtain ⟨rs', hex', hsc'⟩ := hThn N leafSpec rsg
    refine ⟨rs', RustExec.seq _ _ rs rsg rs' hexg
      (RustExec.ifTrue guardSlot thn' els' rsg rs'
        (c.eval rs.rsScalar) hguard hc hex'), ?_⟩
    rw [hsc', hgσ]
    simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte]

/-! ## §4  The proved representative lowering

A single straight-line arithmetic block wrapped in a bounded loop — the
representative program the POC proves correct end to end:

```rust
// source (RustSrc):
let acc = 0u64;
for i in 0..4 {
    let t = i * 3u64;
    acc = (acc + t) ^ 5u64;
}
```

`exampleSrc` is its `RustSrc` encoding; `exampleProgRefines` proves the lowered
LowCT command denotes the source semantics, discharged through the §3
compilation lemmas via `lowerRefines` (the structural driver) — *not* a bespoke
`RustExec` induction. -/

/-- The representative source program (straight-line arithmetic inside a bounded
    loop). All `if`-free, so within the proved fragment. -/
def exampleSrc : RustSrc :=
  .letE "acc" (.SLit 0)
    (.forN "i" 4
      (.letE "t" (.SMul (.SVar "i") (.SLit 3))
        (.assign "acc"
          (.SXor (.SAdd (.SVar "acc") (.SVar "t")) (.SLit 5)))))

/-- `exampleSrc` is in the `if`-free fragment (so `lowerRefines` applies). -/
theorem exampleSrc_ifFree : exampleSrc.ifFree = true := by
  simp [exampleSrc, RustSrc.ifFree]

/-- **The proved representative lowering.** The lowered LowCT command
    `lower exampleSrc` denotes the source semantics `exampleSrc.exec` — i.e. for
    any fuel, leaf spec, and start state, `RustExec` runs the lowering to a state
    whose scalar map is exactly the source program's. Discharged through the §3
    relational-compilation lemmas (via `lowerRefines`); no bespoke induction. -/
theorem exampleProgRefines : RRefines (RustSrc.exec exampleSrc) (lower exampleSrc) :=
  lowerRefines exampleSrc exampleSrc_ifFree

/-- Spelled-out corollary: the lowered command, run under `RustExec` from any
    state, lands in a state whose scalar map equals the source semantics applied
    to the start scalar map. This is the concrete "compiled code ≡ spec" fact the
    security-front / perf-front bridge consumes. -/
theorem exampleProg_exec_denotes (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    ∃ rs', RustExec N leafSpec (lower exampleSrc) rs rs' ∧
      rs'.rsScalar = RustSrc.exec exampleSrc rs.rsScalar :=
  exampleProgRefines N leafSpec rs

/-- Sanity check that the source semantics computes the expected concrete value
    (the loop folds `acc := (acc + 3i) ^ 5` for `i = 0,1,2,3` from `acc = 0`):
    `((((((0)^5 ... )))) = 12`. Confirms the `RRefines` statement is non-vacuous
    — the proved equation pins `acc` to a concrete result, not an opaque term. -/
example : RustSrc.exec exampleSrc (fun _ => 0) "acc" = 26 := by native_decide

/-! ## §5  Scope report — what the full lowering needs (honest)

This module is the **POC skeleton + one proved representative lowering**. It is
**not** a verified Rust frontend. What it *is*: a verified lowering
`(RustSrc) → (LowCT / LowCT)` for the `if`-free scalar subset
(`skip/assign/seq/letE/forN`), proved correct against `RustExec` via a
relational-compilation relation (`RRefines`) assembled from reusable compilation
lemmas — the LowCT analogue of the VIR-emitter `Refines` framework.

### Trust note (net trust reduction, not elimination)

The verified part is `(RustSrc) → LowCT`. The unverified part is `Rust →
hax-AST (`ImpExpr`) → RustSrc`: hax's frontend (Rust → `ImpExpr`) is an external,
unverified tool, and the `ImpExpr → RustSrc` desugaring is, for this POC,
described but not mechanised. So the end-to-end chain is **trusted
`Rust → RustSrc` + verified `RustSrc → LowCT`**.

The payoff is a *net trust reduction*: today each protocol carries a per-protocol
`LeafAgrees` / `FrontValueAgrees` hypothesis — an *assumed* agreement between the
abstract spec's leaf and the compiled leaf. For code the lowering covers, that
hypothesis is **replaced by a proved fact** (the lowered LowCT denotes the source
semantics). The assumption moves from "spec leaf ≡ compiled leaf, assumed" to
"hax read the Rust faithfully, assumed" — a strictly smaller and more uniform
trusted base (one frontend, not one bridge hypothesis per protocol).

### Rest of the subset (constructors to add)

* **Fixed-size arrays.** `LowCT` already has `TArr n t`, `RArrStore`/`RArrLoad`
  (runtime index) and `RArrStoreLit`/`RArrLoadLit` (literal index). Lowering
  `a[i] = e` / `let v = a[i]` is the corresponding constructor; correctness needs
  a `RRefines`-style lemma over the *tower heap* (`rsTower`) rather than the
  scalar map, so it engages `LeafSpec.arrStore`/`arrLoad` (the oracle). This is
  where the relation widens from "scalar-map equality" to "scalar-map ∧ tower-heap
  agreement".
* **`u32`/`u64` width tracking.** Present as `TU32`/`TU64`; lowering must thread
  the declared width so `SExpr` operations wrap at the right modulus. The scalar
  model here is `Nat` (`rsScalar`); a width-faithful version interprets each slot
  as `BitVec w` — a refinement of the state model, not a new relation shape.
* **Function calls.** `f(args)` → `RCall` / `RCallN` / `RFnCall`; correctness is a
  *modular* `RRefines` over the callee's spec (a Hoare-style frame rule), the LowCT
  analogue of the VIR framework's leaf-call lemma `Refines.leafRotr`.
* **`if` guard framing.** §3.4 proves the `if` lowering against the *honest*
  guard-clobbering spec. The residual is choosing `guardSlot` fresh (a gensym
  threaded through `lower`) and **framing it out** of the observable post-state,
  recovering the clean `if c then specThn else specEls` spec. This is the LowCT
  analogue of the VIR emitter's slot-disjointness side conditions.
* **A driving tactic.** §3.3's `lowerRefines` is a structural recursion (the
  subset's first-order syntax needs no CPS-continuation elaborator). A full
  lowering with gensym/framing benefits from a `rupicola_rust` tactic that
  discharges the freshness side conditions automatically — the direct counterpart
  of `RelationalCompile.scont_peel` / `rupicola`.

### The borrowck → borrowOk synergy

`LowCT` carries a static memory-safety predicate `borrowOk`
(`LowCTBorrowCheck.lean`): e.g. every `RCall dest args` requires `dest ∉ args`,
every `RCallN` requires `dests` mutually distinct and disjoint from `args`. These
are exactly the obligations **Rust's own borrow checker discharges**: an `&mut`
destination cannot alias an `&`/`&mut` argument, mutable borrows are exclusive.

So the full lowering gets `borrowOk` *for free* from a well-borrow-checked Rust
source: the lowering can **emit a `borrowOk` proof alongside the LowCT command**,
justified by the source having type-checked under Rust's borrow rules (the hax
frontend already only accepts borrow-checked Rust). This turns Rust's borrow
checker into the discharge mechanism for LowCT's aliasing side conditions — a
borrowck → borrowOk synergy that removes the manual `borrowOk` proofs the
back-end currently needs per kernel. (The scalar subset proved here has no
aliasing obligations — scalar slots are value-copied — so `borrowOk` is trivial;
the synergy bites once arrays / calls enter, per the constructor list above.)
-/

end CatCrypt.Crypto.Hax.RustSubsetToLowCT
