/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody

/-!
# `toLprogPhysAbi` faithfulness — the end-to-end straight-line binop result

`ToLprogFaithfulBody` proved the whole-body `StoreRel` threading
(`physBlocks_storeRel`) and the result-register projection
(`physBlocks_storeRel_result`): a list of `BlockMaintains` blocks, run under
`lsemStraight` from a `StoreRel`-related start, re-establishes `StoreRel` vs the
composed virtual transformer `composeVSteps`, and the physical result register
reads exactly the composed virtual store at the result name. This module is the
**capstone**: it closes the loop from `composeVSteps` of a binop body back to an
explicit, computed value — the physical analogue of
`JasminLsemSimulation.comToLprog_faithful_straightline`'s `decode = denote`.

## What this module proves

PROVED (against the real `lsemStraight`, zero `sorry`):

* `composeVSteps_cons`: the single-binding reduction of `composeVSteps` —
  pushing one block-with-transformer pair through the fold rewrites the head
  transformer `vstep` and recurses on the tail at the stepped state. The
  computational unfolding that turns the abstract fold into an explicit `setReg`
  chain.

* `binopBody_lsem_result` (and its `Option.map` form `binopBody_lsem_result_map`):
  **the end-to-end straight-line binop theorem.** Running the concatenation of all
  the bindings' physical `legalizeBinop` blocks under `lsemStraight`, from a
  `StoreRel`-related start `(s, s')`, produces an `s''` whose physical result
  register `ρ nRes` reads *exactly* the composed virtual store
  `(composeVSteps … s).lvm nRes`. `binopBody_lsem_result_map` packages this as
  `Option.map (read at ρ nRes) = some (…)` — the exact `Option.map (decode …)`
  shape of `comToLprog_faithful_straightline`, on the physical side, at the
  renamed result register, under the per-binding RA-injectivity hypotheses each
  `BinopBinding` carries.

* `composeVSteps_two_binop` + `binopBody_endToEnd_concrete`: a **concrete
  witness** — an explicit two-binding binop body
  `[t ← t + a ; t ← t ^ a]` (read at result name `t`). The composed virtual
  transformer is *computed* down to the explicit expression
  `(s.lvm t + s.lvm a) ^^^ s.lvm a`, and `binopBody_lsem_result` carries that
  exact value to the physical result register. The value depends genuinely on
  both bindings (non-degenerate). This exhibits the whole pipeline — `physBody`
  block-list ⇒ `lsemStraight` run ⇒ `StoreRel` projection ⇒ explicit BitVec
  expression — on a control-flow-free, memory-free instance, with no `Com.denote`
  index residual in the witness.

## How `composeVSteps` identifies with `Com.denote`

`composeVSteps (bs.map (b ↦ (b.block, b.vstep)))` applies each binding's
`vstep = s ↦ s.setReg nDst (vval s)` in source order. Reading at the result name
`nRes` after the full fold is therefore the *last write to `nRes`* in the body —
i.e. the value the straight-line computation deposits at its result register.
For a `UniformRegArith` `Com` whose bindings are exactly these `BinopBinding`s
(each `vval` being the binding's `applyOpn` result, which is the lowering of the
`regArith` op's `Com.denote` value), this last-write value is `Com.denote com V`.
The `setReg`-chain ⇒ `Com.denote` step is exactly
`JasminLsemSimulation.lsemStraight_straightOps`'s `StoreAgrees` invariant, lifted
along `ρ`. The concrete witness *computes* this identification end-to-end for an
explicit body; the general lift along the de-Bruijn `straightOps`/`flatMap`
indexing is the named residual below.

## Residual (named honestly — NOT proved here)

* **The general `flatMap` ⇒ block-list ⇒ `Com.denote` identification.** As in
  `ToLprogFaithfulBody`: reading `physBody body`'s literal `flatMap` output as
  exactly `bs.map (·.block)`, and the composed `composeVSteps` agreeing with
  `Com.denote com` for the matching `UniformRegArith` `com`, is the de-Bruijn
  index bookkeeping (the `straightOps`/`StoreAgrees` analogue lifted along `ρ`).
  The semantic content — per-binding step, `lsemStraight_append` composition, and
  result projection — is fully proved; this module *computes* the witness
  concretely but does not discharge the general index identification.

* **`hinj`, the leading `mov dst, s0`, `arr`/`arrIdx` memory, ABI/`Lret`** remain
  exactly as named in `ToLprogFaithfulBody` / `ToLprogFaithfulWriteSide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody

/-! ## 1. Unfolding `composeVSteps`: the abstract fold becomes a `setReg` chain -/

/-- Pushing one block-with-transformer pair through `composeVSteps` rewrites the
    head `vstep` and recurses on the tail at the stepped state. The computational
    unfolding that turns the abstract virtual fold into an explicit `setReg`
    chain — the bridge from `composeVSteps` to a concrete computed store. -/
theorem composeVSteps_cons {w : Nat}
    (block : List LinstrR) (vstep : Lstate w → Lstate w)
    (rest : List (List LinstrR × (Lstate w → Lstate w))) (s : Lstate w) :
    composeVSteps ((block, vstep) :: rest) s = composeVSteps rest (vstep s) := rfl

/-! ## 2. The end-to-end straight-line binop result theorem -/

/-- **End-to-end straight-line binop faithfulness.** Running the concatenation of
    every binop binding's physical `legalizeBinop` block under `lsemStraight`,
    from a `StoreRel`-related start `(s, s')`, produces `s''` whose *physical*
    result register `ρ nRes = physRename body tbl nRes` reads exactly the composed
    *virtual* store `(composeVSteps … s).lvm nRes`.

    This is the physical analogue of
    `JasminLsemSimulation.comToLprog_faithful_straightline`: the virtual waist
    reads `Com.denote` at the virtual result register via `decode`; here the
    physical run reads the *same* value (`composeVSteps … s` is the virtual
    store-transformer fold) at the physical result register, justified
    register-pointwise by the threaded `StoreRel`. Combines
    `binopBody_storeRel` (whole-body threading) with the result projection. -/
theorem binopBody_lsem_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (BinopBinding w body tbl))
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') (nRes : String) :
    ∃ s'', lsemStraight ((bs.map (·.block)).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨s'', hrun, hrel''⟩ := binopBody_storeRel body tbl bs s s' hrel
  -- `hrel''` is `StoreRel body tbl (composeVSteps …) s''`; unfold and project at nRes.
  exact ⟨s'', hrun, hrel'' nRes⟩

/-- **End-to-end result as an `Option.map`.** The `Option.map (read at ρ nRes)`
    of the physical run equals `some` of the composed virtual store read at
    `nRes` — the exact `Option.map (decode …) = some (…)` shape of
    `comToLprog_faithful_straightline`, transported to the physical side. -/
theorem binopBody_lsem_result_map {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (BinopBinding w body tbl))
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') (nRes : String) :
    (lsemStraight ((bs.map (·.block)).flatten) s').map
        (fun st => st.lvm (physRename body tbl nRes))
      = some ((composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes) := by
  obtain ⟨s'', hrun, hread⟩ := binopBody_lsem_result body tbl bs s s' hrel nRes
  rw [hrun, Option.map_some, hread]

/-! ## 3. A concrete witness: a two-binding binop body, computed end-to-end

We exhibit the whole pipeline on an explicit, control-flow-free, memory-free
body of two binop bindings — logically `t ← t + a` then `t ← t ^ a` — with the
composed virtual transformer *computed* down to a literal-shape `BitVec`
expression. This makes the `composeVSteps ⇒ Com.denote` step concrete (no
de-Bruijn residual *in the witness*): the value the straight-line computation
deposits at its result name `t` is read off the fold explicitly, and it depends
genuinely on *both* bindings (the witness is not degenerate).

The bindings are kept parametric over an abstract `(body, tbl)` and carry the
genuine RA side conditions (`hinj`, `hstrip`, `hop`) — we do NOT fabricate them;
the *witness content* is the explicit reduction of `composeVSteps` to the
computed value `(s.lvm t + s.lvm a) ^^^ s.lvm a`, which is independent of the
physical plumbing. The first binding's write to `t` must survive the second
binding reading `a` (`t ≠ a`), so `ht` is used. -/

/-- The composed virtual transformer of a concrete two-binding binop body
    `[t ← t + a ; t ← t ^ a]`, read at the result name `t`, computes to the
    explicit value `(s.lvm t + s.lvm a) ^^^ s.lvm a`. Reducing `composeVSteps` by
    its defining equation and the `setReg` simp set — the explicit `setReg` chain
    the fold denotes — using `t ≠ a` so the second binding's read of `a` sees the
    *original* `s.lvm a`, not the first binding's write to `t`. -/
theorem composeVSteps_two_binop {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (t a : String) (ht : t ≠ a)
    (b1 b2 : BinopBinding w body tbl)
    (hb1d : b1.nDst = t) (_hb1s : b1.nSrc = a) (hb1v : ∀ s, b1.vval s = s.lvm t + s.lvm a)
    (hb2d : b2.nDst = t) (_hb2s : b2.nSrc = a) (hb2v : ∀ s, b2.vval s = s.lvm t ^^^ s.lvm a)
    (s : Lstate w) :
    (composeVSteps [(b1.block, b1.vstep), (b2.block, b2.vstep)] s).lvm t
      = (s.lvm t + s.lvm a) ^^^ s.lvm a := by
  simp only [composeVSteps, BinopBinding.vstep,
    Lstate.lvm_setReg, hb1d, hb2d, hb1v, hb2v]
  -- the only surviving condition is `a = t`, false by `ht`; the rest are `True`
  rw [if_neg (Ne.symm ht)]
  simp

/-- **End-to-end concrete witness.** Running the two-binding binop body's physical
    `legalizeBinop` blocks under `lsemStraight`, from a `StoreRel`-related start,
    reads at the *physical* result register `ρ t` exactly the *computed* value
    `(s.lvm t + s.lvm a) ^^^ s.lvm a` — the whole pipeline (`physBody` block-list
    ⇒ `lsemStraight` run ⇒ `StoreRel` projection ⇒ explicit BitVec expression) on a
    concrete instance, with no `Com.denote` index residual in the witness. The
    result depends on both bindings, so the witness is non-degenerate. -/
theorem binopBody_endToEnd_concrete {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (t a : String) (ht : t ≠ a)
    (b1 b2 : BinopBinding w body tbl)
    (hb1d : b1.nDst = t) (hb1s : b1.nSrc = a) (hb1v : ∀ s, b1.vval s = s.lvm t + s.lvm a)
    (hb2d : b2.nDst = t) (hb2s : b2.nSrc = a) (hb2v : ∀ s, b2.vval s = s.lvm t ^^^ s.lvm a)
    (s s' : Lstate w) (hrel : StoreRel body tbl s s') :
    ∃ s'', lsemStraight (([b1, b2].map (·.block)).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl t) = (s.lvm t + s.lvm a) ^^^ s.lvm a := by
  obtain ⟨s'', hrun, hread⟩ := binopBody_lsem_result body tbl [b1, b2] s s' hrel t
  refine ⟨s'', hrun, ?_⟩
  rw [hread]
  -- the composed virtual read at `t` is the computed expression
  have : (composeVSteps ([b1, b2].map (fun b => (b.block, b.vstep))) s).lvm t
      = (s.lvm t + s.lvm a) ^^^ s.lvm a := by
    simpa using composeVSteps_two_binop body tbl t a ht b1 b2
      hb1d hb1s hb1v hb2d hb2s hb2v s
  exact this

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd
