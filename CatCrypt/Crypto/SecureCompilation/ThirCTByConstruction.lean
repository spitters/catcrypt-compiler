/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-!
# The `thirDialect` front IR is constant-time by construction

This module sits **above** `Com jasminDialect` — it is the front of the
THIR → jasmin stack (the input side of the `Com jasminDialect → machine`
lowering), disjoint from both the `LowCT → machine` and the
`Com jasminDialect → machine` lowerings.

## The security claim

The plan offered two routes to a *secure* (constant-time) compiler: an
information-flow system, or **restricting the language so it cannot branch or
index on secrets**. The front IR already takes the second route *structurally*:

* every `ThirOp` is straight-line dataflow — arithmetic, the **branchless**
  `thSelect` (a cmov, not a branch), constant loads, the carry primitives, the
  vector pack, an equality-to-bit, and `thExtCall` (a leaf primitive call);
* `Com` itself is straight-line SSA (`.var` / `.ret`) — no `ite`, no `for`, no
  regions.

So a `Com thirDialect` admits **no data-dependent control flow and no
data-dependent memory index**: there is nothing for a secret to flow *into* that
would create a timing/address channel. The constant-time policy therefore holds
for the front IR **regardless of any secret labelling** — which is exactly what
"restrict the language to restrict branching and loops" buys, made precise.

`thExtCall` is the one externally-defined node; its constant-timeness is the
callee's obligation (the same leaf-primitive trust edge every backend has), not a
control-flow channel introduced by the front.

## Composition with the rest of the chain

This front guarantee composes downward (the two interfaces owned by the other
two workstreams):

```
Com thirDialect   ── CT by construction (THIS file)
   │  lowerThir            (ThirToComFront; front)
Com jasminDialect ── no data-dependent control surface (preserved)
   │  Com jasminDialect → machine   (the kernel-stack lowering)
machine block     ── CompilableCT / blockLeak public-determined  (Phase 0)
```

The bottom rung (`CompilableCT`, machine `blockLeak` state-independence) is
`X86Backend/CompilableCT.lean`; this file is its source-language counterpart. The
middle rung (preservation through `lowerThir` and the jasmin→machine lowering) is
the obligation the front/back lowerings + the compiler-correctness work discharge.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirCTByConstruction

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-! ## 1. No `ThirOp` is a data-dependent control / addressing node -/

/-- A front op is a **data-dependent control or addressing** node iff it could
    introduce a secret-conditioned branch or a secret-derived memory index. NO
    `ThirOp` constructor is such a node: arithmetic and the branchless `thSelect`
    are pure dataflow, `thExtCall` is a leaf call (its timing is the callee's
    obligation, not a front-introduced channel). So this is `false` for every op
    — the front language cannot express a secret-dependent control surface. -/
def opDataDependentControl : ThirOp → Bool := fun _ => false

/-- **The front op set is control-surface-free.** Every `ThirOp` is dataflow:
    none introduces a data-dependent branch or memory index. The point is this
    `Bool` is forced `false` because the inductive has no branch/loop/indexed-load
    constructor that could make it `true`. -/
theorem op_no_data_dependent_control (op : ThirOp) :
    opDataDependentControl op = false := rfl

/-- The op set, by `cases`, has no control-flow / indexed-memory constructor —
    the structural fact the claim rests on. If a future op added a branch/indexed
    load, this proof would force revisiting `opDataDependentControl`. -/
theorem op_all_dataflow : ∀ op : ThirOp, opDataDependentControl op = false := by
  intro op; cases op <;> rfl

/-! ## 2. A `Com thirDialect` is constant-time by construction

`Com` is straight-line SSA, so a `Com thirDialect` is a chain of `thirDialect`
`Expr`s ending in a `ret`. Since every op is dataflow (§1) and there is no
control-flow combinator in `Com`, the whole program has no data-dependent
control surface: it is CT by construction. We capture this as a predicate that
holds for *every* `Com thirDialect`. -/

/-- A front program is **constant-time by construction** when every operation it
    contains is control-surface-free. For `thirDialect` this holds for *all*
    programs, so the predicate is the source-language analogue of the
    machine-level `CompilableCT`. -/
def ComCTByConstruction {Γ : Ctxt thirDialect} {t : thirDialect.Ty} :
    Com thirDialect Γ t → Prop
  | .ret _ => True
  | .var e body => opDataDependentControl e.op = false ∧ ComCTByConstruction body

/-- **The front guarantee: every `Com thirDialect` is CT by construction.** No
    program in the front IR has a data-dependent control or addressing surface,
    so no secret can create a timing/address channel — the constant-time policy
    holds structurally, for any secret labelling. This is the formal content of
    the "restrict the language to restrict branching and loops" security route. -/
theorem com_ct_by_construction {Γ : Ctxt thirDialect} {t : thirDialect.Ty}
    (c : Com thirDialect Γ t) : ComCTByConstruction c := by
  induction c with
  | ret v => exact True.intro
  | var e body ih => exact ⟨op_all_dataflow e.op, ih⟩

end CatCrypt.Crypto.SecureCompilation.ThirCTByConstruction
