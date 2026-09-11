/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeHoist
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# The `invntt` hoist as a SYNTACTIC loop pass over the lattice dialect

`LatticeHoist.lean` proves the `invntt`-out-of-the-loop fusion as a
**denotation-level** fold-fusion theorem (`latticeHoist_eq`, built on the
dialect-agnostic core `latticeHoist_generic`). This file lifts that result into
an actual **loop construct** and exposes the optimization as a
denotation-preserving *pass* over that construct: a source bounded accumulate-
loop that runs `invntt` once per iteration (coefficient domain) rewrites to a
target loop that accumulates in the NTT domain and applies a single closing
`invntt`.

This is the lattice analog of `JasminPrint.JForProg` (the bounded-for loop
construct over the Jasmin dialect): a self-contained loop whose **denotation is
a `List.foldl`**, so it plugs directly into `latticeHoist_eq`. Where `JForProg`
folds a fixed update over `List.range n`, the lattice loop folds an
accumulate-update over a **list of input pairs** — the `polyvec_dot` shape
`Σ_i ⟨a_i, b_i⟩` whose per-term contribution is a coefficient-form product.

## The pass

```
src:  acc := 0; for (a_i, b_i) in pairs { acc := polyAddN acc (polyMulC a_i b_i) }
                                                              -- invntt per iteration
                            ││  hoistLatticeDot
                            ▼▼
tgt:  acc := 0; for (a_i, b_i) in pairs { acc := polyAddN acc (basemul (ntt a_i)(ntt b_i)) }
      ret invntt acc                                         -- single closing invntt
```

The contribution of each term is computed by a per-iteration body that is an
honest `Com latticeDialect` (the source body is exactly `srcCom`'s
`polyMulC`-shaped multiply threaded through an accumulator add; the target body
is the NTT-domain `basemul` add). We expose those bodies and prove their
`Com.denote` equals the foldl step functions (`rfl`), so the loop denotation is
genuinely a fold over `Com`-level iterations — then state and discharge the
hoist over the loop denotations by reusing `latticeHoist_eq`.

## What is modelled vs. represented as a fold

As in `JForProg`, the loop is represented by its **fold denotation** (a total
`List.foldl`, exactly what a bounded loop denotes); no SSA-phi wiring of the
carried accumulator across iterations is introduced. The per-iteration
*contribution* is a real `Com latticeDialect` whose denotation we prove equal
to the step. The deliverable is therefore: a loop representation (fold of
`Com`-level iterations) + a denotation-preserving hoist rewrite reusing the
verified fusion core `latticeHoist_eq`/`latticeHoist_generic`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## §1  The bounded accumulate-loop construct

`LatticeDotLoop` mirrors `JForProg`: a self-contained loop carrying its data
(here, the list of input pairs) and a per-iteration accumulator update, with a
total denotation by `List.foldl`. Unlike `JForProg` (which folds a fixed update
over `List.range n`), the per-iteration contribution is drawn from the list of
input pairs — the `polyvec_dot` shape. `acc` and `contribution` are the same
underlying representation `Fin n → BitVec 16` (the shared denotation of `polyC`
and `polyN`). -/

/-- A bounded accumulate-loop over a list of polynomial input pairs. `pairs`
    supplies one `(·, ·)` per iteration; `step acc a b` folds the contribution
    of pair `(a, b)` into the accumulator; `z` is the initial accumulator.

    Its denotation (`LatticeDotLoop.denote`) is a `List.foldl`, exactly the
    semantics of a bounded loop, and the shape that `latticeHoist_*` consumes. -/
structure LatticeDotLoop (n : Nat) where
  /-- One input pair per loop iteration (the `polyvec_dot` operands). -/
  pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))
  /-- Per-iteration accumulator update: fold pair `(a, b)` into `acc`. -/
  step : (Fin n → BitVec 16) → (Fin n → BitVec 16) → (Fin n → BitVec 16) →
    (Fin n → BitVec 16)
  /-- Initial accumulator. -/
  z : Fin n → BitVec 16

/-- Total denotation of the loop: left-fold `step` over `pairs` from `z`. This
    is the bounded-loop semantics — no fuel, the iteration count is `pairs.length`. -/
def LatticeDotLoop.denote {n : Nat} (p : LatticeDotLoop n) : Fin n → BitVec 16 :=
  p.pairs.foldl (fun acc q => p.step acc q.1 q.2) p.z

/-! ## §2  The per-iteration term contributions as honest `Com latticeDialect`

Each iteration's *contribution* is computed by a real `Com latticeDialect`. The
dialect has a single accumulator op `polyAddN` (NTT-domain add, only on
`polyN`), so — exactly as in `latticeHoist_eq`, which folds with `polyAddNF` on
both sides — the loop's accumulator combine is `polyAddNF` and the **term
contribution** is the per-iteration `Com`:

* **source** (`srcMulCom`): `let c = polyMulC a b; ret c` over `[a, b] : polyC`,
  computing `polyMulCF a b` — one `invntt` baked into `polyMulC`.
* **target** (`tgtMulCom`): `let ta = ntt a; let tb = ntt b; ret (basemul ta tb)`
  over `[a, b] : polyC`, computing `basemulF (nttF a) (nttF b)` — the NTT-domain
  contribution, no per-iteration `invntt`.

This is the canonical `srcCom`/`tgtCom` split of `LatticeDialect.lean`, here the
loop body. We prove each `Com.denote` equals the contribution function it stands
for. -/

section Bodies

variable (q n : Nat)

/-- Per-iteration term context: the two coefficient-form inputs `[a, b]`
    (`a` at `.here`, `b` at `.there .here`). -/
@[reducible] def stepCtxt : Ctxt latticeDialect :=
  [.polyC q n, .polyC q n]

/-- **Source per-iteration contribution** (`Com`): `let c = polyMulC a b; ret c`.
    Computes `polyMulCF a b` — one `invntt` baked into `polyMulC` per iteration,
    coefficient domain. (This is `LatticeDialect.srcCom` reused as the loop body.) -/
def srcMulCom : Com latticeDialect (stepCtxt q n) (.polyC q n) :=
  -- c = polyMulC a b   (a : `here`, b : `there here`)
  .var (.mk (.polyMulC q n) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **Target per-iteration contribution** (`Com`):
    `let ta = ntt a; let tb = ntt b; let c = basemul ta tb; ret c`.
    Computes `basemulF (nttF a) (nttF b)` — the NTT-domain contribution, no
    per-iteration `invntt`. (This is `LatticeDialect.tgtCom` minus its closing
    `invntt`, reused as the loop body.) -/
def tgtMulCom : Com latticeDialect (stepCtxt q n) (.polyN q n) :=
  -- ta = ntt a   (a : `here`)
  .var (.mk (.ntt q n) rfl (.cons .here .nil))
  -- tb = ntt b   (b : now `there (there here)`)
  (.var (.mk (.ntt q n) rfl (.cons (.there (.there .here)) .nil))
    -- c = basemul ta tb   (ta : `there here`, tb : `here`)
    (.var (.mk (.basemul q n) rfl
            (.cons (.there .here) (.cons .here .nil)))
      (.ret .here)))

/-- The source contribution's `Com.denote` equals `polyMulCF a b`. By
    definition (`rfl`): the `polyMulC` op denotes to exactly that leaf. -/
theorem srcMulCom_denote (a b : Fin n → BitVec 16) :
    (srcMulCom q n).denote (.cons a (.cons b .nil)) = polyMulCF a b := rfl

/-- The target contribution's `Com.denote` equals `basemulF (nttF a) (nttF b)`.
    By definition. -/
theorem tgtMulCom_denote (a b : Fin n → BitVec 16) :
    (tgtMulCom q n).denote (.cons a (.cons b .nil))
      = basemulF (nttF a) (nttF b) := rfl

end Bodies

/-! ## §3  The source and target loops

`srcLoop` accumulates the coefficient-domain contribution each iteration (an
`invntt` per term, baked into `polyMulCF`); `tgtLoop` accumulates the NTT-domain
contribution and is followed by a single closing `invntt`. The per-iteration
contribution is *exactly* the denotation of `srcMulCom`/`tgtMulCom`, folded with
the accumulator combinator `polyAddNF` (matching `latticeHoist_eq`), so each loop
is a fold of `Com`-level iterations. -/

variable {n : Nat}

/-- **Source loop** (`polyvec_dot`, coefficient domain): per iteration
    `acc := polyAddN acc (polyMulC a b)`, initialised at `default` (the zero
    polynomial). One `invntt` per term. The contribution is `srcMulCom`'s
    denotation. -/
def srcLoop (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    LatticeDotLoop n :=
  { pairs := pairs
    step := fun acc a b => polyAddNF acc (polyMulCF a b)
    z := default }

/-- **Target loop** (NTT domain): per iteration
    `acc := polyAddN acc (basemul (ntt a) (ntt b))`, initialised at `default`.
    No per-iteration `invntt`; one is applied to the final accumulator
    (`tgtLoopClosed`). The contribution is `tgtMulCom`'s denotation. -/
def tgtLoop (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    LatticeDotLoop n :=
  { pairs := pairs
    step := fun acc a b => polyAddNF acc (basemulF (nttF a) (nttF b))
    z := default }

/-- The source loop's per-term contribution is `srcMulCom`'s denotation: each
    iteration folds the `Com`-computed coefficient-domain product into `acc`. -/
theorem srcLoop_step_eq_com
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16)))
    (q : Nat) (acc a b : Fin n → BitVec 16) :
    (srcLoop pairs).step acc a b
      = polyAddNF acc ((srcMulCom q n).denote (.cons a (.cons b .nil))) := by
  show polyAddNF acc (polyMulCF a b)
      = polyAddNF acc ((srcMulCom q n).denote (.cons a (.cons b .nil)))
  rw [srcMulCom_denote]

/-- The target loop's per-term contribution is `tgtMulCom`'s denotation: each
    iteration folds the `Com`-computed NTT-domain product into `acc`. -/
theorem tgtLoop_step_eq_com
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16)))
    (q : Nat) (acc a b : Fin n → BitVec 16) :
    (tgtLoop pairs).step acc a b
      = polyAddNF acc ((tgtMulCom q n).denote (.cons a (.cons b .nil))) := by
  show polyAddNF acc (basemulF (nttF a) (nttF b))
      = polyAddNF acc ((tgtMulCom q n).denote (.cons a (.cons b .nil)))
  rw [tgtMulCom_denote]

/-! ## §4  The hoist pass: source loop ↦ target loop + single `invntt`

The headline. The source loop's denotation equals `invntt` of the target
loop's denotation — i.e. the per-iteration `invntt` (baked into `polyMulC`)
hoists out to a single closing `invntt`. Proven by **reusing** `latticeHoist_eq`
(which is itself `latticeHoist_generic`, the verified fold-fusion core). -/

/-- **The hoist (denotation-preserving).** `srcLoop.denote = invntt (tgtLoop.denote)`:
    the source loop (one `invntt` per term, coefficient domain) and the NTT-domain
    target loop followed by a single closing `invntt` denote to the same
    polynomial. Reuses `latticeHoist_eq` (⇐ `latticeHoist_generic`). -/
theorem hoistLatticeDot
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    (srcLoop pairs).denote = invnttF ((tgtLoop pairs).denote) := by
  -- Both `denote`s unfold to the folds `latticeHoist_eq` relates.
  show pairs.foldl (fun acc q => polyAddNF acc (polyMulCF q.1 q.2)) default
      = invnttF (pairs.foldl
          (fun acc q => polyAddNF acc (basemulF (nttF q.1) (nttF q.2))) default)
  exact latticeHoist_eq pairs

/-- Closed-form target program: the NTT-domain loop with the single closing
    `invntt` applied. This is the rewritten ("hoisted") program; `hoistLatticeDot`
    states it denotes equal to `srcLoop`. -/
def tgtLoopClosed
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    Fin n → BitVec 16 :=
  invnttF ((tgtLoop pairs).denote)

/-- Restated against the closed-form target: `srcLoop.denote = tgtLoopClosed`.
    This is the pass's full input-output equivalence. -/
theorem hoistLatticeDot_closed
    (pairs : List ((Fin n → BitVec 16) × (Fin n → BitVec 16))) :
    (srcLoop pairs).denote = tgtLoopClosed pairs :=
  hoistLatticeDot pairs

/-! ## §5  Smoke test

A concrete `pairs` list at `(q, n) = (3329, 2)`, checking the pass closes
(`srcLoop.denote = tgtLoopClosed`) by the theorem and computing the expected
value of the dot product. We reuse `smokeA`/`smokeB` from `LatticeDialect`. -/

/-- Two pairs: `[(a, b), (b, a)]` over the ML-KEM-flavoured `(3329, 2)` setting. -/
def smokePairs : List ((Fin 2 → BitVec 16) × (Fin 2 → BitVec 16)) :=
  [(smokeA, smokeB), (smokeB, smokeA)]

/-- The pass closes on the concrete list (a special case of `hoistLatticeDot`). -/
theorem smoke_hoist :
    (srcLoop smokePairs).denote = tgtLoopClosed smokePairs :=
  hoistLatticeDot_closed smokePairs

/-- The source loop computes the expected dot value. With `a = (7, 35)`,
    `b = (6, 2)`: term 1 = `(7*6, 35*2) = (42, 70)`, term 2 = `(6*7, 2*35) = (42, 70)`,
    sum from `0` = `(84, 140)`. (Function equality: split `Fin 2`, `decide`.) -/
theorem smoke_dot_value :
    (srcLoop smokePairs).denote
      = (fun i => if i = 0 then (84 : BitVec 16) else 140) := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- And the (hoisted) target loop computes the same value, via `smoke_hoist`. -/
theorem smoke_dot_value_tgt :
    tgtLoopClosed smokePairs
      = (fun i => if i = 0 then (84 : BitVec 16) else 140) := by
  rw [← smoke_hoist]; exact smoke_dot_value

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
