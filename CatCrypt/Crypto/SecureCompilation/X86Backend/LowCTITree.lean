/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Plain interaction-tree (free-monad) denotational layer with calls as events

This module builds a **minimal, iris-free interaction-tree** denotational layer
for the compiler IR fragment in which *external calls are visible events*, and
proves it is a **conservative extension** of the big-step denotation
`srcDenote` on the call-free bounded fragment.

We follow the *plain*-ITree approach (arXiv:2511.11292) — **not** the
guarded/Iris ITrees.  Because the control flow in our bounded fragment stays
unrolled (no loops at this layer), there is **no nontermination**, so we use an
ordinary `inductive` free monad (no `Tau` constructor, no coinduction).  The
interaction-tree structure is used *only* to expose external/leaf calls as
events with a continuation; the terminating scalar-arith fragment denotes to a
pure `ret`.

## What lives here

* `EventSig` — a local, minimal event signature `(Event : Type, Resp : ·)`.
  This is deliberately *not* the `UCMonad.ITreeN` signature (that one drags in
  `SPComp`/`RoundM`, is noncomputable and probabilistic — we want a light,
  deterministic, terminating free monad).
* `CallTree E R` — the free monad: `ret` (pure result) and `vis` (an event with
  a response-indexed continuation).
* `CallTree.bind` with the two monad identity laws.
* `interp h` — a *handler* `h` that answers every event, folding the tree to its
  result.
* `Stmt` — a statement: either a pure scalar `ArithSrc` step or an external
  `scall f args dst` (call function `f`, bind its returned word to slot `dst`).
* `callEvents` — the call event signature: an event carries the callee name and
  the argument *values*; the response is the returned 64-bit-faithful word
  (a `Nat`, kept consistent with `RustState.rsScalar`).
* `itreeDenote : List Stmt → RustState → CallTree callEvents RustState` — the
  interaction-tree denotation: a scalar step continues purely, a call emits a
  `vis` event whose continuation resumes from the post-call state.

## The conservative-extension theorem (the Phase-4 point)

* `itreeDenoteArith ps rs = CallTree.ret (srcDenote ps rs)`
  (`itreeDenote_callfree`): the ITree denotation of a **call-free** program is a
  pure `ret` of the big-step result — no `vis` ever arises.
* `interp h (itreeDenoteArith ps rs) = srcDenote ps rs`
  (`interp_itreeDenote_callfree`): interpreting recovers the big-step result.
  This **is** the conservative-extension statement: the ITree layer agrees with
  the big-step `srcDenote` on the bounded, call-free fragment.

For the call-bearing case, `interp_scall` shows the handler resolves a call
event and the interpretation resumes from the handler-supplied return word —
the Phase-4 call-composition hook.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-! ## 1. A local, minimal event signature -/

/-- A minimal **event signature**: a type of events `Event`, and for each event a
    type `Resp e` of admissible responses.  This is the local, light version of
    an interaction signature; it is **not** the `UCMonad.ITreeN` one (that drags
    in `SPComp`/`RoundM` and is probabilistic/noncomputable). -/
structure EventSig where
  Event : Type
  Resp : Event → Type

/-! ## 2. The free monad (terminating fragment: inductive, no `Tau`) -/

/-- The **plain interaction tree** over an event signature `E`, a free monad:
    `ret r` is a pure result; `vis e c` performs event `e` and continues with `c`
    indexed by the response.  No `Tau`/coinduction — the bounded fragment is
    terminating, so an ordinary inductive suffices. -/
inductive CallTree (E : EventSig) (R : Type) where
  | ret : R → CallTree E R
  | vis : (e : E.Event) → (E.Resp e → CallTree E R) → CallTree E R

/-! ## 3. Monadic bind and the identity laws -/

/-- Monadic bind for `CallTree`: `ret a >>= k = k a`; a `vis` node threads `k`
    into the continuation. -/
def CallTree.bind {E : EventSig} {α β : Type} :
    CallTree E α → (α → CallTree E β) → CallTree E β
  | .ret a,    k => k a
  | .vis e c,  k => .vis e (fun r => (c r).bind k)

/-- **Left identity**: `bind (ret a) k = k a` (definitional). -/
@[simp] theorem CallTree.bind_ret_left {E : EventSig} {α β : Type}
    (a : α) (k : α → CallTree E β) :
    (CallTree.ret a).bind k = k a := rfl

/-- **Right identity**: `bind t ret = t`.  By induction on the tree (the `vis`
    case uses funext on the continuation). -/
@[simp] theorem CallTree.ret_bind {E : EventSig} {α : Type} (t : CallTree E α) :
    t.bind CallTree.ret = t := by
  induction t with
  | ret a => rfl
  | vis e c ih => simp only [CallTree.bind]; exact congrArg (CallTree.vis e) (funext ih)

/-! ## 4. The handler / interpreter -/

/-- **Interpret** a tree under a handler `h` that answers *every* event with a
    response.  `ret r` returns `r`; `vis e c` feeds `h e` into the continuation
    and recurses.  For a `vis`-free (call-free) tree this returns the `ret`
    payload unchanged. -/
def interp {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e) :
    CallTree E R → R
  | .ret r   => r
  | .vis e c => interp h (c (h e))

@[simp] theorem interp_ret {E : EventSig} {R : Type}
    (h : ∀ e : E.Event, E.Resp e) (r : R) :
    interp h (CallTree.ret r) = r := rfl

@[simp] theorem interp_vis {E : EventSig} {R : Type}
    (h : ∀ e : E.Event, E.Resp e) (e : E.Event) (c : E.Resp e → CallTree E R) :
    interp h (CallTree.vis e c) = interp h (c (h e)) := rfl

/-! ## 5. The call-bearing statement and its event signature -/

/-- A statement of the call-bearing fragment: either a pure scalar-arith step
    (`sarith p`, reusing the `ArithSrc` step of the big-step bridge) or an
    external **call** `scall f args dst` — call function `f` on argument slots
    `args`, binding the returned word to slot `dst`. -/
inductive Stmt where
  | sarith : ArithSrc → Stmt
  | scall  : (f : String) → (args : List String) → (dst : String) → Stmt
  deriving Repr

/-- A **call event**: the callee name and the argument *values* (resolved from
    the source state at call time).  The response is the returned word, kept as
    a `Nat` to stay consistent with `RustState.rsScalar`. -/
structure CallEvent where
  f : String
  args : List Nat
  deriving Repr, DecidableEq

/-- The **call event signature**: events are `CallEvent`, each answered by a
    single returned word (`Nat`). -/
@[implicit_reducible]
def callEvents : EventSig where
  Event := CallEvent
  Resp := fun _ => Nat

/-! ## 6. The interaction-tree denotation: calls as visible events -/

/-- **The ITree denotation.**  A scalar step continues *purely* (it updates the
    source state exactly as `srcDenote` does, then recurses with no event); a
    `scall f args dst` emits a **visible `vis` event** carrying the callee and
    the resolved argument values, whose continuation resumes denotation from the
    post-call state `rsSetScalar rs dst ret`.  This is calls-as-visible-events
    with a continuation — the semantic object Phase 4 needs. -/
def itreeDenote : List Stmt → RustState → CallTree callEvents RustState
  | [],                rs => .ret rs
  | (.sarith p) :: ts, rs =>
      itreeDenote ts (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar))
  | (.scall f args dst) :: ts, rs =>
      .vis (E := callEvents) ⟨f, args.map rs.rsScalar⟩
        (fun ret => itreeDenote ts (rsSetScalar rs dst ret))

@[simp] theorem itreeDenote_nil (rs : RustState) :
    itreeDenote [] rs = .ret rs := rfl

@[simp] theorem itreeDenote_sarith (p : ArithSrc) (ts : List Stmt) (rs : RustState) :
    itreeDenote (.sarith p :: ts) rs =
      itreeDenote ts (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) := rfl

@[simp] theorem itreeDenote_scall (f : String) (args : List String) (dst : String)
    (ts : List Stmt) (rs : RustState) :
    itreeDenote (.scall f args dst :: ts) rs =
      .vis (E := callEvents) ⟨f, args.map rs.rsScalar⟩
        (fun ret => itreeDenote ts (rsSetScalar rs dst ret)) := rfl

/-! ## 7. The pure scalar fragment and conservative extension -/

/-- The ITree denotation specialised to the **call-free** scalar fragment: a
    `List ArithSrc` (no `scall` can occur).  This is `itreeDenote` on the image
    of `.sarith`. -/
def itreeDenoteArith (ps : List ArithSrc) (rs : RustState) :
    CallTree callEvents RustState :=
  itreeDenote (ps.map Stmt.sarith) rs

@[simp] theorem itreeDenoteArith_nil (rs : RustState) :
    itreeDenoteArith [] rs = .ret rs := rfl

@[simp] theorem itreeDenoteArith_cons (p : ArithSrc) (ps : List ArithSrc)
    (rs : RustState) :
    itreeDenoteArith (p :: ps) rs =
      itreeDenoteArith ps (rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)) := by
  simp [itreeDenoteArith]

/-- **Conservative extension (call-free fragment).**  The ITree denotation of a
    call-free scalar-arith program is a pure `ret` of the big-step result
    `srcDenote` — **no `vis` event ever arises**.  Proven by induction on the
    program: every step is `.sarith`, so denotation only updates state and
    recurses.  This is the core P4.1 agreement: the ITree layer collapses to the
    big-step denotation on the bounded, call-free fragment. -/
theorem itreeDenote_callfree (ps : List ArithSrc) (rs : RustState) :
    itreeDenoteArith ps rs = CallTree.ret (srcDenote ps rs) := by
  induction ps generalizing rs with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- **Conservative extension, interpreted (the conservative-extension statement).**
    Interpreting the ITree denotation of a call-free program under *any* handler
    `h` recovers the big-step result `srcDenote`.  Since the tree is `vis`-free,
    the handler is never consulted.  This is the conservative-extension corollary:
    the ITree denotational layer agrees with the big-step `srcDenote` on the
    bounded call-free fragment. -/
theorem interp_itreeDenote_callfree (h : ∀ e : callEvents.Event, callEvents.Resp e)
    (ps : List ArithSrc) (rs : RustState) :
    interp h (itreeDenoteArith ps rs) = srcDenote ps rs := by
  rw [itreeDenote_callfree]; rfl

/-! ## 8. Calls are resolved by the handler (the Phase-4 composition hook) -/

/-- **The handler resolves a call.**  Interpreting a call-bearing program under
    a handler `h` consumes the leading `scall` by feeding the handler's answer
    `h ⟨f, args⟩` into the continuation: interpretation resumes from the
    post-call state `rsSetScalar rs dst (h ⟨f, args-values⟩)`.  This shows the
    call event is handled — the Phase-4 call-composition hook. -/
theorem interp_scall (h : ∀ e : callEvents.Event, callEvents.Resp e)
    (f : String) (args : List String) (dst : String) (ts : List Stmt)
    (rs : RustState) :
    interp h (itreeDenote (.scall f args dst :: ts) rs) =
      interp h (itreeDenote ts
        (rsSetScalar rs dst (h ⟨f, args.map rs.rsScalar⟩))) := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
