/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve

/-!
# P4.4: whole-function call composition (programs *with* calls)

This module lifts the Phase-4 results — compiler correctness as a `rHoare`
judgment (`callfree_compile_rHoare`, P4.1/P4.2) and cryptographic-security
preservation (`compiled_preserves_security`, P4.3) — from the **call-free**
scalar-arith fragment to **whole functions**, i.e. programs that interleave
scalar segments with external **calls** (`scall`/`vis`).

The composition principle is the `vis` (call) structure of the
interaction-tree layer:

* A whole function is a `List Stmt` mixing `sarith` scalar steps and `scall`s.
  Its `interpSP` denotation threads each call through the handler `h` via the
  `vis`-bind law `interpSP_vis`:
  `interpSP h (vis e k) = (h e) >>= fun resp => interpSP h (k resp)`.
* At every call the event `e = ⟨f, args.map rs.rsScalar⟩` and the handler `h`
  are **identical on both sides** — the call is the *same handler invocation*.
  This is the point where an adversarial / oracle context enters; because the
  linked context (the handler) is the same on both sides, the **same-handler
  bind-congruence** threads that (possibly adversarial) context through
  identically.  That is the robust-against-context step.
* Between calls, the deterministic compiler preserves the scalar segments'
  big-step semantics (`srcDenote`).  Equal `srcDenote` per segment ⇒ the two
  whole-function ITree denotations are *equal* ⇒ their `interpSP` denotations
  are equal ⇒ (via `spDenote_eq_preserves_sdist`) the `sdist` security bound is
  preserved.

So compiler correctness + security preservation **compose through calls**: by
induction on the program, the scalar case reuses the call-free agreement, and
the call case closes with the pРHL `bind`-congruence on the *same* handler call.

## Segmented whole functions

To make "same call structure, scalar segments agree" precise we model a whole
function as a list of `CallSeg`s — each a scalar segment (`List ArithSrc`)
optionally followed by one call.  `segToStmts` flattens it to a `List Stmt`.
Two segment lists with **identical calls** and **per-segment-equal `srcDenote`**
denote equally (`itreeDenote_segs_eq`); this is the compiler-correctness
congruence threaded through the call (`vis`) structure.

## What lives here

* `CallSeg`, `segToStmts` — the segmented whole-function model.
* `itreeDenote_append_arith` — a scalar segment prefix folds to `srcDenote`
  (the call-free agreement, reused inside a larger program).
* `itreeDenote_segs_eq` — **the call-composition congruence**: identical calls
  + per-segment-equal `srcDenote` ⇒ equal whole-function `itreeDenote`.  By
  induction on the segment list; the scalar prefix uses the call-free fold and
  the call step is the *same* `vis` node (identical event + identical handler),
  closed by `congrArg` on the continuation (the term-level same-handler
  bind-congruence; its `rHoare` form is `rHoare_bind` with `c₁ = c₂ = h e`).
* `interpSP_segs_eq` — the same equality lifted to `interpSP`.
* `wholeFn_progEquiv` — `progEquiv` at the `SPComp` level for whole functions:
  identical calls + per-segment-equal `srcDenote` ⇒ equal `interpSP`.
* `wholeFn_compile_rHoare` — **relational compiler correctness for whole
  functions** (with calls): the `rHoare` analogue of `callfree_compile_rHoare`,
  via `wholeFn_progEquiv` + `rHoare_refl`-style return reasoning.
* `wholeFn_preserves_security` — **the P4.4 capstone**: cryptographic / UC
  security (`sdist ≤ ε` to an ideal) is preserved for whole compiled functions
  (call-bearing), by composing `wholeFn_progEquiv` with
  `spDenote_eq_preserves_sdist` — exactly as `compiled_preserves_security` did
  for the call-free fragment, now lifted through calls.

## The call step is the same-handler bind-congruence (= robust-against-context)

The exact pRHL rule for the call step is `rHoare_bind` applied with the **same
head computation** `c₁ = c₂ = h e` on both sides: relating
`(h e) >>= k₁` against `(h e) >>= k₂`.  The head judgment is `rHoare_refl`-style
(identical computation, equal heaps), and the continuations are related by the
induction hypothesis.  At the term level (when the two sides are *equal*) this
is `congrArg (SPComp.bind (h e))` on the continuation.  Either way the call is
the *same handler invocation* on both sides — the handler is the linked
(possibly adversarial) context, threaded through identically.

## Iris-free

Imports only `LowCTSecPreserve` (which transitively pulls `LowCTITree`,
`LowCTITreePRHL`, `CatCrypt.Relational.Rules`, `CatCrypt.Core`, and
`CatCrypt.Crypto.SDist`).  Nothing under `Bridges/` or `IrisBridge/`: no guarded
ITrees, no step-indexing, no separation logic.  Bounded (terminating) fragment.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Relational
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
open scoped ENNReal

/-! ## 1. A scalar segment prefix folds to the big-step `srcDenote`

A run of `sarith` steps prepended to an arbitrary rest-program denotes by first
threading the scalar segment exactly as `srcDenote` does, then continuing with
the rest from the post-segment state.  This is the call-free agreement
(`itreeDenote_callfree`) *reused inside* a larger, call-bearing program: it is
what lets us collapse each inter-call scalar segment to its `srcDenote`. -/

/-- **Scalar-segment prefix law.**  The ITree denotation of a scalar segment
    `ps` (as `sarith` steps) followed by an arbitrary rest-program `ts` equals
    the denotation of `ts` started from the post-segment big-step state
    `srcDenote ps rs`.  Proven by induction on the segment, reusing the
    big-step fold of `srcDenote`. -/
theorem itreeDenote_append_arith (ps : List ArithSrc) (ts : List Stmt)
    (rs : RustState) :
    itreeDenote (ps.map Stmt.sarith ++ ts) rs =
      itreeDenote ts (srcDenote ps rs) := by
  induction ps generalizing rs with
  | nil => simp [srcDenote]
  | cons p ps ih =>
      simp only [List.map_cons, List.cons_append, itreeDenote_sarith, srcDenote_cons]
      exact ih _

/-! ## 2. The segmented whole-function model -/

/-- A **call segment**: a scalar segment `scalars` (a `List ArithSrc`) optionally
    followed by a single external call `call = some (f, args, dst)`.  A whole
    function is a `List CallSeg`: alternating scalar work and calls.  This makes
    "same call structure" precise (identical `call` fields) and lets the scalar
    segments be transformed by the compiler (changing `scalars` while preserving
    its `srcDenote`). -/
structure CallSeg where
  scalars : List ArithSrc
  call    : Option (String × List String × String)

/-- Flatten one call segment to a `List Stmt`: the scalar steps as `sarith`,
    then the optional trailing `scall`. -/
def CallSeg.toStmts (s : CallSeg) : List Stmt :=
  s.scalars.map Stmt.sarith ++
    (match s.call with
     | none => []
     | some (f, args, dst) => [Stmt.scall f args dst])

/-- Flatten a whole function (a list of call segments) to a `List Stmt`. -/
def segToStmts : List CallSeg → List Stmt
  | []        => []
  | s :: rest => s.toStmts ++ segToStmts rest

@[simp] theorem segToStmts_nil : segToStmts [] = [] := rfl

@[simp] theorem segToStmts_cons (s : CallSeg) (rest : List CallSeg) :
    segToStmts (s :: rest) = s.toStmts ++ segToStmts rest := rfl

/-! ## 3. The call-composition congruence (the heart of P4.4)

Two whole functions with **identical call structure** (segment lists of equal
length with equal `call` fields) whose **inter-call scalar segments agree**
big-step (`srcDenote`-equal as functions) have **equal `itreeDenote`**.

The induction has two kinds of step:

* **scalar prefix** — collapses via `itreeDenote_append_arith`; the two segments
  having equal `srcDenote` land in the *same* post-segment state, so the rest
  continues from identical states.
* **call (`vis`)** — both sides emit the *same* `vis` node: identical event
  `⟨f, args.map rs.rsScalar⟩` (same `f`, `args`, and identical state) with the
  continuation resuming from `rsSetScalar rs dst ret`.  Since the node is the
  same and the continuations agree by the induction hypothesis, the trees are
  equal (`congrArg (CallTree.vis e)` on the continuation — the term-level
  same-handler congruence; its probabilistic / `rHoare` form is `rHoare_bind`
  with `c₁ = c₂ = h e`).  This is where the (possibly adversarial) context
  enters identically on both sides. -/

/-- Per-segment hypothesis: the two segment lists have the **same length**,
    **identical calls**, and **per-segment-equal `srcDenote`** (the scalar
    segments are compiler-transformed but big-step-equivalent). -/
def SegsAgree : List CallSeg → List CallSeg → Prop
  | [],        []        => True
  | _ :: _,    []        => False
  | [],        _ :: _    => False
  | s₁ :: r₁,  s₂ :: r₂  =>
      s₁.call = s₂.call ∧
      (∀ rs : RustState, srcDenote s₁.scalars rs = srcDenote s₂.scalars rs) ∧
      SegsAgree r₁ r₂

/-- **The call-composition congruence.**  Identical call structure + per-segment
    `srcDenote` agreement ⇒ equal whole-function `itreeDenote` from *any* start
    state.  By induction on the segment lists: the scalar prefix collapses via
    `itreeDenote_append_arith` (so both sides reach the same post-segment state),
    and the call step is the *same* `vis` node, closed by `congrArg` on the
    continuation (the term-level same-handler bind-congruence). -/
theorem itreeDenote_segs_eq :
    ∀ (segs₁ segs₂ : List CallSeg), SegsAgree segs₁ segs₂ →
      ∀ rs : RustState, itreeDenote (segToStmts segs₁) rs
                       = itreeDenote (segToStmts segs₂) rs
  | [], [], _, rs => by simp
  | s₁ :: r₁, s₂ :: r₂, hag, rs => by
      obtain ⟨hcall, hsrc, hrest⟩ := hag
      simp only [segToStmts_cons, CallSeg.toStmts]
      -- peel the scalar segment on both sides via the prefix law
      rw [List.append_assoc, List.append_assoc,
          itreeDenote_append_arith, itreeDenote_append_arith]
      -- both segments reach the same post-segment state
      rw [hsrc rs]
      set rs' := srcDenote s₂.scalars rs with hrs'
      -- now match on the (identical) call fields
      cases hc1 : s₁.call with
      | none =>
          have hc2 : s₂.call = none := by rw [← hcall, hc1]
          simp only [hc2, List.nil_append]
          exact itreeDenote_segs_eq r₁ r₂ hrest rs'
      | some c =>
          obtain ⟨f, args, dst⟩ := c
          have hc2 : s₂.call = some (f, args, dst) := by rw [← hcall, hc1]
          simp only [hc2, List.singleton_append, itreeDenote_scall]
          -- same vis node; continuations agree by IH
          refine congrArg (CallTree.vis (E := callEvents) ⟨f, args.map rs'.rsScalar⟩) ?_
          funext ret
          exact itreeDenote_segs_eq r₁ r₂ hrest (rsSetScalar rs' dst ret)

/-! ## 4. The congruence lifted to `interpSP`

Equal `itreeDenote` ⇒ equal `interpSP` (it is a function of the tree).  This is
`progEquiv` at the `SPComp` level for *whole* (call-bearing) functions.  The
call (`vis`) steps go through `interpSP_vis` identically on both sides — the
*same* handler call `h e` bound into agreeing continuations — so the
denotations coincide. -/

/-- **`interpSP` call-composition congruence.**  Whole functions with identical
    call structure and per-segment `srcDenote` agreement have **equal
    `interpSP`** denotations, under *any* `SPComp`-valued handler `h`.  Immediate
    from `itreeDenote_segs_eq` (equal trees) since `interpSP h` is a function of
    its tree argument.  Each `vis` (call) is the *same* `h e`-bind on both sides
    (`interpSP_vis`) — the same-handler bind-congruence. -/
theorem interpSP_segs_eq
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (segs₁ segs₂ : List CallSeg) (hag : SegsAgree segs₁ segs₂) (rs : RustState) :
    interpSP h (itreeDenote (segToStmts segs₁) rs)
      = interpSP h (itreeDenote (segToStmts segs₂) rs) := by
  rw [itreeDenote_segs_eq segs₁ segs₂ hag rs]

/-! ## 5. `progEquiv` and relational compiler correctness for whole functions -/

/-- **Whole-function `progEquiv` at the `SPComp` level.**  This is the
    call-bearing analogue of `interpSP_progEquiv`: two whole functions with
    identical call structure and per-segment-equal `srcDenote` (the deterministic
    compiler preserves each scalar segment's big-step semantics, and leaves the
    call structure intact) interpret to **equal** `SPComp` computations.  It is
    `interpSP_segs_eq`, named to mirror the call-free lemma. -/
theorem wholeFn_progEquiv
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (segs₁ segs₂ : List CallSeg) (hag : SegsAgree segs₁ segs₂) (rs : RustState) :
    interpSP h (itreeDenote (segToStmts segs₁) rs)
      = interpSP h (itreeDenote (segToStmts segs₂) rs) :=
  interpSP_segs_eq h segs₁ segs₂ hag rs

/-- **Relational compiler correctness for whole functions (with calls), as
    pRHL.**  The call-bearing analogue of `callfree_compile_rHoare`.  Two whole
    functions with identical call structure and per-segment-equal `srcDenote`
    have `interpSP` denotations that are **equal**, hence trivially `rHoare`-
    related for the diagonal "equal-results-and-heaps" postcondition under any
    precondition `Φ`.

    Proved by rewriting the right side to the left via `wholeFn_progEquiv`
    (compiler correctness threaded through the call structure) and closing the
    residual identical-computation judgment with `rHoare_refl`-style reasoning
    (`rHoare_bind` on the *same* handler call composes each `vis` step; with the
    two sides definitionally equal it collapses to reflexivity).  This is the
    whole-function relational compiler-correctness statement. -/
theorem wholeFn_compile_rHoare
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (segs₁ segs₂ : List CallSeg) (hag : SegsAgree segs₁ segs₂)
    (rs : RustState) :
    rHoare CatCrypt.Relational.eqPre
      (interpSP h (itreeDenote (segToStmts segs₁) rs))
      (interpSP h (itreeDenote (segToStmts segs₂) rs))
      CatCrypt.Relational.eqPost := by
  rw [wholeFn_progEquiv h segs₁ segs₂ hag rs]
  exact CatCrypt.Relational.rHoare_refl _

/-! ## 6. The P4.4 capstone: security preservation for whole functions -/

/-- **P4.4: whole compiled functions preserve cryptographic security.**

    Let `srcSegs` be a source whole function (call-bearing) and `tgtSegs` its
    compilation, with `hag : SegsAgree srcSegs tgtSegs` — the compiler keeps the
    call structure intact and preserves each inter-call scalar segment's big-step
    `srcDenote`.  If the *source* function's `interpSP` denotation is `ε`-close
    (in `sdist`) to an `ideal` computation, then so is the *compiled* function's.

    Security preservation is obtained **by composition through the call
    structure**: `wholeFn_progEquiv` (compiler correctness threaded through every
    `vis`/call as the *same* handler invocation) gives equal `SPComp`
    denotation, which feeds `spDenote_eq_preserves_sdist` (equal denotation ⇒
    same `sdist` bound, the `SPComp`-restated body of
    `SCIO.uc_is_secure_compilation`).  No fresh probabilistic-RHL argument is
    needed: the call-free P4.3 proof lifts to whole functions because each call
    is the same handler call on both sides (the linked, possibly adversarial,
    context is threaded through identically).

    `(secure compilation via SCIO RrHP + deterministic-to-pure lift, lifted
    through calls)` -/
theorem wholeFn_preserves_security {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (srcSegs tgtSegs : List CallSeg) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hag : SegsAgree srcSegs tgtSegs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenote (segToStmts srcSegs) rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenote (segToStmts tgtSegs) rs))
          (fun _ : α => ideal) ≤ ε :=
  spDenote_eq_preserves_sdist
    (wholeFn_progEquiv h srcSegs tgtSegs hag rs) hsec

/-- **Canonical instance: the same whole function.**  When source and compiled
    whole function are the same (`SegsAgree` reflexive), the bound is preserved
    immediately — the `interpSP` denotation is literally unchanged.  This is the
    `sdist_self`-style degenerate case of `wholeFn_preserves_security`. -/
theorem wholeFn_preserves_security_self {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (segs : List CallSeg) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hag : SegsAgree segs segs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenote (segToStmts segs) rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (itreeDenote (segToStmts segs) rs))
          (fun _ : α => ideal) ≤ ε :=
  wholeFn_preserves_security h segs segs rs ideal hag hsec

/-! ## 7. `SegsAgree` is reflexive

Every whole function agrees with itself (the compiler's identity transform): the
calls are equal and each scalar segment's `srcDenote` equals itself.  This
witnesses that the hypothesis of the capstone is inhabited (non-vacuous) and
supplies the reflexive instance used by `wholeFn_preserves_security_self`. -/

/-- `SegsAgree` is reflexive: a whole function agrees with itself. -/
theorem SegsAgree_refl : ∀ segs : List CallSeg, SegsAgree segs segs
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ => rfl, SegsAgree_refl rest⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose
