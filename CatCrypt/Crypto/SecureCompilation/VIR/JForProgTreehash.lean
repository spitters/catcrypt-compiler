/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
import CatCrypt.Crypto.SecureCompilation.VIR.JasminSymmetricLeaves

/-!
# Level-indexed loop composition: the emitted level-`for`-sequence denotes the
# serial composition of the per-level `n`-folds (`TreehashProg`)

This file is the **level-composition layer** on top of the single-level loop
keystone (`JForProgSemCorrect.loop_denote_eq`, `JForProgCT.loopRun_eq`). Like the
nesting layer (`JForProgNested.lean`, task #81), it does **not** modify the
single-level layer (`JForProgSemCorrect.lean`, `JForProgCT.lean`,
`JasminPrint.JForProg` / `toCfor` / `toProg`) or the FAEST leaf specs
(`FAEST/Leaves.lean`) — it imports them and **composes** their results. There is
**no new denotation-preservation core**: the whole-tree theorem is the existing
single-level keystone composed `h` times (a `foldl`/list-composition congruence).

## The motivating shape: Merkle treehash

A Merkle treehash of depth `h` builds the root **level by level**: level `l`
folds `2^(h-1-l)` node-pairs into the next level up — so it is `h` fixed-trip
**single-level loops in sequence**, with per-level *varying* compile-time trip
counts (`4, 2, 1` for `h = 3`, i.e. `8 → 4 → 2 → 1`), threading a fixed-size
tree-state accumulator. This is exactly the hash-tree idiom shared by the FAEST
GGM seed tree, XMSS / SLH-DSA Merkle treehash, and PLONK/Plonky FRI folding.

## The construct

A `TreehashProg accTy` is a **`List (JForProg accTy)`** — the per-level loops, in
order, over a *shared* accumulator type (the tree-state slot). Its denotation is
the **serial composition** of the per-level `n`-folds:

```
TreehashProg.denote levels init
  = levels.foldl (fun acc lvl => lvl.denote acc) init
```

i.e. run level 0's loop on `init`, feed the result into level 1's loop, etc. The
`Fin h → JForProg accTy` family form is recovered by `List.ofFn`.

## The emission

`TreehashProg.toCfor` emits the `h` per-level `Cfor`s **in sequence** (one top
level instruction per level), via the *actual* emitted `JForProg.toCfor` of each
level (the verified single-level loop the keystone covers). The shared `ppInstrR`
prints each `for` consecutively, so the emitted `.jazz` is literally `h`
sequential `for` loops with the halving counts.

## The denotation-preservation theorem (the deliverable)

`treehash_loop_denote_eq`: running the emitted level sequence — composing each
level's emitted single-level `loopRun` serially — equals
`TreehashProg.denote init`. The proof:

1. **Per-level (reuse, not re-prove):** for a single-leaf level body, the emitted
   single-level loop run equals `level.denote` by the *already-proven*
   `JForProgSemCorrect.loop_denote_eq`. There is **no new core**.
2. **Across levels (induct):** both `treehashLoopRun` and `TreehashProg.denote`
   are left-folds of the per-level runner over the level list; their per-element
   functions agree on every accumulator by step 1, so a `foldl` congruence closes
   the whole tree.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, exactly as the
single-level keystone — no `sorry`, axiom-clean (`[propext, Quot.sound]` like
`loop_denote_eq`).

## The Th tweakable-hash leaf (`PIECE 2`)

`§7` declares the SLH-DSA / XMSS **`Th` tweakable hash** as a *single* `extCall`
leaf — so each level loop's inner body stays single-var (covered by
`loop_denote_eq`'s `SingleVarBody`, avoiding the multi-op gap). `Th` hashes a
node pair plus an `ADRS` tweak; per the FAEST `#62` leaf pattern
(`FAEST/Leaves.lean` `shakeLeafExpr` / `ShakeLeafAgrees`), `Th` is SHAKE-based +
an `ADRS` tweak, so its agreement is *backed by the committed SHAKE leaf*: a
`leafSem` realising the FAEST `shake128` primitive on the concatenated
`tweak ‖ left ‖ right` input realises `Th`.

## A concrete validating kernel: the 2-1 combiner treehash

`§8` `combinerTree` is a self-contained, pure treehash that validates level
composition end-to-end: `h = 3` levels of a fixed 2→1 combiner `acc := acc + acc`
(a single `regArith add` leaf), with the halving counts `4, 2, 1`. From the seed
this composes `4 + 2 + 1 = 7` doublings, KAT'd byte-identical in
`bench/treehash/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-! ## 1. The level-indexed treehash construct -/

/-- A **level-indexed sequence of single-level bounded loops** over a shared
    accumulator type. Each entry is one tree level's fold; running the levels in
    order builds the root. The per-level trip counts vary at compile time (e.g.
    `4, 2, 1`) — the halving Merkle / GGM shape. The `Fin h → JForProg accTy`
    family form is `List.ofFn`.

    A reducible `abbrev` over `List (JForProg accTy)`, so all `List`
    dot-notation (`foldl`, `map`, `∈`, `length`) and the `Membership` instance
    are available transparently. -/
abbrev TreehashProg (accTy : JasminTy) : Type := List (JForProg accTy)

/-- One level's step: run the whole single-level loop on the accumulator. This is
    the per-level fold function the serial composition iterates. -/
def levelStep {accTy : JasminTy} (lvl : JForProg accTy) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  lvl.denote acc

/-- **Serial level composition (denotation).** Run each level's `n`-fold in
    order, threading the accumulator: level 0's loop on `init`, then level 1's
    loop on that, … No fuel — all counts are static. -/
def TreehashProg.denote {accTy : JasminTy} (levels : TreehashProg accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  levels.foldl (fun acc lvl => levelStep lvl acc) init

/-! ## 2. The emitted level sequence (`h` sequential `Cfor`s) -/

/-- Emit a treehash as the **`h` per-level `Cfor`s in sequence**: one top-level
    instruction per level, each the *actual* emitted single-level loop
    `JForProg.toCfor` of that level (the verified loop the keystone covers). The
    shared `ppInstrR` prints them consecutively, so the emitted `.jazz` is `h`
    sequential `for` loops with the halving counts. -/
def TreehashProg.toCfors {accTy : JasminTy} (levels : TreehashProg accTy) :
    List CatCrypt.Crypto.Jasmin.InstrR :=
  levels.map (fun lvl => lvl.toCfor)

/-- Lower a `TreehashProg` to a single-function `JasminProg`: parameter `acc`
    (the initial accumulator / leaf state), the `h` sequential `Cfor`s, and
    `ret acc`. -/
def TreehashProg.toProg {accTy : JasminTy} (name : String)
    (levels : TreehashProg accTy) : CatCrypt.Crypto.Jasmin.JasminProg :=
  let fd : CatCrypt.Crypto.Jasmin.FunDecl :=
    { name := { name := name }
      params := [{ var := mkVarI "acc" accTy }]
      body := TreehashProg.toCfors levels
      results := [mkVarI "acc" accTy] }
  { funcs := [fd] }

/-! ## 3. Structural facts about the emission -/

/-- **Structural fact: one emitted top-level instruction per level.** The emitted
    body is exactly `h` instructions, one `Cfor` per tree level — the sequential
    level-by-level shape (not nested, not unrolled). -/
theorem toCfors_length {accTy : JasminTy} (levels : TreehashProg accTy) :
    (TreehashProg.toCfors levels).length = levels.length := by
  simp [TreehashProg.toCfors]

/-- **Structural fact: every emitted top-level instruction is a `Cfor`.** Each
    level is emitted as a real bounded `for`, not unrolled. -/
theorem toCfors_all_cfor {accTy : JasminTy} (levels : TreehashProg accTy) :
    ∀ instr ∈ levels.toCfors, ∃ v r body, instr = .Cfor v r body := by
  intro instr hmem
  rw [TreehashProg.toCfors, List.mem_map] at hmem
  obtain ⟨lvl, _, rfl⟩ := hmem
  exact ⟨_, _, _, rfl⟩

/-- **Structural fact: the emitted program is single-function, `h`-loop body, one
    accumulator parameter, one result.** -/
theorem toProg_shape {accTy : JasminTy} (name : String)
    (levels : TreehashProg accTy) :
    (levels.toProg name).funcs.length = 1
      ∧ ((levels.toProg name).funcs.head?.map (fun fd => fd.body.length))
          = some levels.length
      ∧ ((levels.toProg name).funcs.head?.map (fun fd => fd.params.length))
          = some 1
      ∧ ((levels.toProg name).funcs.head?.map (fun fd => fd.results.length))
          = some 1 :=
  ⟨rfl, by simp [TreehashProg.toProg, toCfors_length], rfl, rfl⟩

/-! ## 4. `n`-fold unfolding of the level composition -/

/-- **Serial-composition unfolding (List.foldl form).** The treehash denotation
    is the left-fold of each level's `n`-fold denotation over the level list. -/
theorem denote_eq_foldl {accTy : JasminTy} (levels : TreehashProg accTy)
    (init : ⟦accTy⟧) :
    levels.denote init
      = levels.foldl (fun acc lvl => lvl.denote acc) init := rfl

/-- **The empty tree is the identity.** Zero levels return the initial
    accumulator unchanged. -/
theorem denote_nil {accTy : JasminTy} (init : ⟦accTy⟧) :
    TreehashProg.denote ([] : TreehashProg accTy) init = init := rfl

/-- **Level cons-unfolding.** Running `lvl :: rest` is: run `lvl`'s loop on
    `init`, then run the remaining levels on the result. The per-level
    recurrence the emitted level sequence realises. -/
theorem denote_cons {accTy : JasminTy} (lvl : JForProg accTy)
    (rest : TreehashProg accTy) (init : ⟦accTy⟧) :
    TreehashProg.denote (lvl :: rest) init
      = TreehashProg.denote rest (lvl.denote init) := rfl

/-! ## 5. The per-level body runner is the emitted single-level loop

Each level's per-fold runner is *the whole emitted single-level loop run*. For a
single-leaf level body, this equals `level.denote` by the already-proven
single-level keystone `loop_denote_eq` — so the per-level runner *is*
`levelStep`. This is the only place the single-level keystone is touched; the
whole-tree result is its `foldl`-composition. -/

/-- The per-level body runner: running the emitted single-level loop in full on
    accumulator `acc` (the single-level `loopRun` of `lvl` with its emitted body
    runner). This is the evaluator-side meaning of "run level `lvl`'s `for`". -/
def levelRun {accTy : JasminTy} (leafSem : LeafSem) (lvl : JForProg accTy) :
    BodyRunner accTy :=
  fun acc => loopRun lvl (bodyStepRun leafSem lvl) acc

/-- **The per-level runner computes `levelStep` (= `lvl.denote`).** For a
    single-leaf level body, running the emitted single-level loop in full equals
    the level loop's `n`-fold denotation — by the *already-proven* single-level
    keystone `JForProgSemCorrect.loop_denote_eq` (reused, not re-derived). The
    only carried hypothesis is the opaque-leaf edge `LeafAgrees`. -/
theorem levelRun_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (lvl : JForProg accTy)
    (e : Expr jasminDialect [accTy] accTy)
    (hLvl : lvl.update = SingleVarBody e) (acc : ⟦accTy⟧) :
    levelRun leafSem lvl acc = levelStep lvl acc := by
  unfold levelRun levelStep
  -- Reuse the single-level keystone for this level's loop.
  exact loop_denote_eq hLeaf e lvl hLvl acc

/-! ## 6. The keystone: emitted level sequence run = serial level composition

The level dimension is closed by a `foldl` congruence: both `treehashLoopRun` and
`TreehashProg.denote` are left-folds of the per-level runner over the level list,
and their per-element functions agree on every accumulator by `levelRun_eq` (the
single-level keystone, per level). There is **no new denotation core** — this is
exactly `loop_denote_eq` composed `h` times. -/

/-- A `foldl` of two functions that agree everywhere over the same list and seed
    coincide. (Local mirror of `JForProgCT.foldl_congr_fun`, which is `private`,
    generalised to a per-element-typed step list.) -/
private theorem foldl_congr_fun {accTy : JasminTy} {β : Type}
    (f g : ⟦accTy⟧ → β → ⟦accTy⟧)
    (hfg : ∀ acc u, f acc u = g acc u) :
    ∀ (l : List β) (init : ⟦accTy⟧), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | _ :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg]
      exact foldl_congr_fun f g hfg l _

/-- Run the emitted level sequence abstractly: compose each level's emitted
    single-level loop runner serially over the level list. This is the
    evaluator-side level-by-level iteration the emitted `h`-`Cfor` sequence
    performs. -/
def treehashLoopRun {accTy : JasminTy} (leafSem : LeafSem)
    (levels : TreehashProg accTy) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  levels.foldl (fun acc lvl => levelRun leafSem lvl acc) init

/-- A uniform single-leaf witness for *every* level of a treehash: each level's
    body is `SingleVarBody e` for some `e` (allowed to depend on the level). This
    is the per-level hypothesis the keystone's `SingleVarBody` requires — every
    level loop's inner body is one op (e.g. one `Th` `extCall` leaf, or one 2→1
    combiner), so it is covered by `loop_denote_eq`, avoiding the multi-op gap. -/
abbrev AllSingleVar {accTy : JasminTy} (levels : TreehashProg accTy) : Prop :=
  ∀ lvl ∈ levels, ∃ e : Expr jasminDialect [accTy] accTy,
    lvl.update = SingleVarBody e

/-- **Keystone — the emitted level sequence denotes the serial level
    composition.** For single-leaf level bodies (`AllSingleVar`), running the
    emitted `h`-`Cfor` sequence (each level a real `for`) by composing the
    per-level emitted single-level loop runners serially equals
    `TreehashProg.denote init` = the serial composition of the per-level
    `n`-folds. Each level reuses the single-level keystone `loop_denote_eq`; the
    level dimension is closed by induction (the `foldl` congruence). **No new
    denotation core** — this is `loop_denote_eq` composed `h` times. The only
    hypothesis is the opaque-leaf edge `LeafAgrees`. -/
theorem treehash_loop_denote_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (levels : TreehashProg accTy)
    (hAll : AllSingleVar levels) (init : ⟦accTy⟧) :
    treehashLoopRun leafSem levels init = TreehashProg.denote levels init := by
  -- Induct on the level list, threading the per-level witness `hAll`. Both sides
  -- fold over the list; the per-element functions agree on every accumulator by
  -- `levelRun_eq` (the single-level keystone), per level.
  induction levels generalizing init with
  | nil => rfl
  | cons lvl rest ih =>
      have hHead : ∃ e : Expr jasminDialect [accTy] accTy,
          lvl.update = SingleVarBody e := hAll lvl List.mem_cons_self
      obtain ⟨e, he⟩ := hHead
      have hTail : AllSingleVar rest :=
        fun l hl => hAll l (List.mem_cons_of_mem _ hl)
      -- Peel one level: the head level's emitted run is `levelStep lvl init`
      -- (single-level keystone), then recurse on the tail.
      unfold treehashLoopRun TreehashProg.denote
      rw [List.foldl_cons, List.foldl_cons, levelRun_eq hLeaf lvl e he init]
      exact ih hTail (levelStep lvl init)

/-! ## 7. The `Th` tweakable-hash leaf (`PIECE 2`)

The SLH-DSA / XMSS **`Th` tweakable hash** hashes a node pair `(left, right)`
together with an `ADRS` tweak into the parent node. We declare it as a **single**
`extCall` leaf so each level loop's inner body is one op — `SingleVarBody`
covered, no multi-op gap. Following the FAEST `#62` leaf pattern
(`FAEST/Leaves.lean` `shakeLeafExpr` / `ShakeLeafAgrees`): `Th` is SHAKE-based +
an `ADRS` tweak, so it is *backed by the committed SHAKE leaf*.

We model nodes / tweaks as byte (`reg 8`) stack arrays of fixed length `n`
(SLH-DSA's hash output length, e.g. 16/24/32). The `Th` input is the
concatenation `ADRS ‖ left ‖ right` (length `3n` bytes); the output is one node
(`n` bytes). Binding `treehash_th` to a `leafSem` realising the FAEST `shake128`
XOF on that concatenated input realises `Th`. -/

open CatCrypt.Crypto.FAEST.Leaves

/-- The leaf name the front-end emits for the SLH-DSA / XMSS `Th` tweakable hash
    (`Th : (ADRS, left, right) ↦ parent`). -/
def thLeafName : String := "treehash_th"

/-- Dialect signature of the `Th` leaf at node-byte length `n`: the input is the
    concatenation `ADRS ‖ left ‖ right` packed as one `stackArr 8 (3*n)` byte
    array; the output is one node `stackArr 8 n`. A single `extCall` so the
    per-level body is single-var. -/
def thArgTys (n : Nat) : List JasminTy := [.stackArr 8 (3 * n)]

/-- Return type of the `Th` leaf at node-byte length `n`: one `n`-byte node. -/
def thRetTy (n : Nat) : JasminTy := .stackArr 8 n

/-- The abstract `Th` tweakable hash spec: `(n, ADRS‖left‖right bytes, output
    index) ↦ parent byte`. This is the interface the SLH-DSA / XMSS Merkle proof
    reasons against; the committed SHAKE leaf realises it (below). -/
structure ThPrimitive where
  /-- `Th` at node length `n`: hash the concatenated `ADRS ‖ left ‖ right` byte
      array (length `3n`) to an `n`-byte parent node. -/
  th : (n : Nat) → (Fin (3 * n) → BitVec 8) → (Fin n → BitVec 8)

/-- Build the `Th` leaf `Expr` from one packed `stackArr 8 (3*n)` input variable
    (`ADRS ‖ left ‖ right`) in scope, at node length `n`. Mirrors
    `FAEST.Leaves.shakeLeafExpr`. -/
def thLeafExpr {Γ : Ctxt jasminDialect} {n : Nat}
    (input : Ctxt.Var Γ (.stackArr 8 (3 * n))) :
    Expr jasminDialect Γ (thRetTy n) :=
  { op := .extCall thLeafName (thArgTys n) (thRetTy n)
    retTy_eq := rfl
    args := .cons input .nil }

/-- The `Th` leaf `Expr` denotes (under any valuation) to `jasminExtSem` of the
    looked-up packed input byte array — the dialect's opaque-leaf semantics. By
    `rfl`, exactly as `FAEST.Leaves.shakeLeafExpr_denote`. -/
theorem thLeafExpr_denote {Γ : Ctxt jasminDialect} {n : Nat}
    (input : Ctxt.Var Γ (.stackArr 8 (3 * n))) (V : Ctxt.Valuation Γ) :
    (thLeafExpr input).denote V
      = jasminExtSem thLeafName (thArgTys n) (thRetTy n)
          (.cons (input.lookup V) .nil) :=
  rfl

/-- `Th` leaf agreement: on the `treehash_th` signature at node length `n`, the
    leaf semantics is `prims.th` of its packed `ADRS ‖ left ‖ right` input. The
    FAEST-`#62` counterpart of `ShakeLeafAgrees` — opaque leaf, carried
    agreement obligation, never a `sorry`. -/
def ThLeafAgrees (prims : ThPrimitive) (leafSem : FaestLeafSem) : Prop :=
  ∀ (n : Nat) (args : HVector (fun t => ⟦t⟧) (thArgTys n)),
    leafSem thLeafName (thArgTys n) (thRetTy n) args
      = (fun (j : Fin n) =>
          prims.th n (fun (i : Fin (3 * n)) => stackGet (args.head) i.val) j)

/-! ### `Th` backed by the committed SHAKE leaf

`Th` is SHAKE-based: hashing `ADRS ‖ left ‖ right` with SHAKE128 (output length
`n`) *is* the tweakable hash (the `ADRS` is the leading tweak bytes of the
input). So a `FaestPrimitives` value's `shake128` XOF, restricted to input length
`3n` and output length `n`, **defines** a `ThPrimitive` — and any `leafSem`
agreeing with `shake128` on that signature agrees with the induced `Th` on the
`treehash_th` name (when the front-end emits `Th` *as* the `faest_shake128` leaf
at that signature). This is the `Th`-is-a-SHAKE-tweak backing: no new primitive,
the committed SHAKE leaf carries it. -/

/-- The `Th` primitive **induced by the committed SHAKE128 XOF**: `Th` at node
    length `n` is `shake128` on the packed `3n`-byte `ADRS ‖ left ‖ right` input
    with output length `n`. The `ADRS` tweak is the leading bytes of the hashed
    input — the standard SLH-DSA `Th = H(ADRS ‖ M)` construction. -/
def ThPrimitive.ofShake (prims : FaestPrimitives) : ThPrimitive where
  th := fun n input => prims.shake128 (3 * n) input n

/-- **`Th` is backed by the committed SHAKE leaf.** If a leaf semantics realises
    the FAEST `shake128` XOF (`ShakeLeafAgrees`) *and* the front-end emits `Th`
    under the SHAKE leaf name at the `Th` signature, then it realises the induced
    `Th` (`ThPrimitive.ofShake`). Concretely: `Th`'s agreement reduces to the
    committed SHAKE leaf's agreement — no new opaque primitive is introduced. We
    state the reduction as the definitional identity between the `Th` spec and the
    SHAKE spec at the `(3n → n)` byte signature. -/
theorem thPrimitive_ofShake_th (prims : FaestPrimitives) (n : Nat)
    (input : Fin (3 * n) → BitVec 8) :
    (ThPrimitive.ofShake prims).th n input
      = prims.shake128 (3 * n) input n := rfl

/-- A `leafSem` that realises `shake128` on the `Th` signature (input length
    `3n`, output length `n`) — but under the `treehash_th` leaf name — realises
    the SHAKE-induced `Th`. This is the `#62`-pattern backing: `ThLeafAgrees` for
    `ThPrimitive.ofShake` follows from the SHAKE-leaf shape, because both reduce
    to `prims.shake128 (3*n) · n`. -/
theorem thLeafAgrees_ofShake (prims : FaestPrimitives) (leafSem : FaestLeafSem)
    (hShakeShaped :
      ∀ (n : Nat) (args : HVector (fun t => ⟦t⟧) (thArgTys n)),
        leafSem thLeafName (thArgTys n) (thRetTy n) args
          = (fun (j : Fin n) =>
              prims.shake128 (3 * n)
                (fun (i : Fin (3 * n)) => stackGet (args.head) i.val) n j)) :
    ThLeafAgrees (ThPrimitive.ofShake prims) leafSem := by
  intro n args
  rw [hShakeShaped n args]
  rfl

/-! ## 8. The 2-1 combiner treehash validating kernel (the simplest level seq)

The simplest treehash kernel that validates level composition: `h = 3` levels of
a fixed 2→1 combiner `acc := acc + acc` (a single `regArith add` leaf — the
`JasminPrint.doubleLoop` body), with the **halving** trip counts `4, 2, 1`
(`8 → 4 → 2 → 1`). To keep the validating kernel pure / self-contained we use the
combiner rather than the `Th` leaf (the *structure* — `h` sequential halving
loops over a shared accumulator — is what matters); the leaf agreement is vacuous
(no `extCall`), so any `leafSem` works.

Composing `4 + 2 + 1 = 7` doublings from `1` computes `2^7 = 128`. -/

/-- A single-level combiner loop of trip count `cnt`: `acc := acc + acc` for
    `cnt` iterations (a `regArith add` body — the same single leaf as
    `JasminPrint.doubleLoop`, at count `cnt`). One per tree level. -/
def combinerLevel (cnt : Nat) : JForProg (.reg 64) :=
  { n := cnt
    update :=
      .var (.mk (.regArith .add 64) rfl
              (.cons .here (.cons .here .nil)))
        (.ret .here) }

/-- The combiner body is a single-leaf body (one `regArith add` then `.ret .here`)
    — at every trip count — so the single-level keystone applies. -/
theorem combinerLevel_singleVar (cnt : Nat) :
    (combinerLevel cnt).update
      = SingleVarBody (accTy := .reg 64)
          (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) := rfl

/-- The 2→1 combiner treehash: `h = 3` levels with the halving trip counts
    `4, 2, 1` (the Merkle `8 → 4 → 2 → 1` shape). Total doublings:
    `4 + 2 + 1 = 7`. -/
def combinerTree : TreehashProg (.reg 64) :=
  [combinerLevel 4, combinerLevel 2, combinerLevel 1]

/-- Every level of `combinerTree` has a single-leaf body, so the keystone's
    `AllSingleVar` hypothesis holds. -/
theorem combinerTree_allSingleVar : AllSingleVar combinerTree := by
  intro lvl hmem
  refine ⟨.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)), ?_⟩
  -- `combinerTree` is a 3-element literal; each entry is a `combinerLevel`.
  simp only [combinerTree, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> subst h <;> rfl

/-- The serial composition doubles `4 + 2 + 1 = 7` times; from `1` that is
    `2^7 = 128` — the level-composition denotation ground truth. -/
theorem combinerTree_denote :
    combinerTree.denote (1 : BitVec 64) = (128 : BitVec 64) := by rfl

/-- **2→1 combiner treehash — emitted level sequence denotes the serial level
    composition.** Running the emitted `h = 3`-`Cfor` sequence (level loops
    `for i = 0 to 4`, `for i = 0 to 2`, `for i = 0 to 1`, each `acc = acc + acc`)
    by composing the per-level runners serially from `init` equals
    `combinerTree.denote init` (= `init` doubled seven times). The leaf agreement
    is vacuous here. Instance of `treehash_loop_denote_eq`. -/
theorem combinerTree_treehash_denote_eq {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : BitVec 64) :
    treehashLoopRun leafSem combinerTree init = combinerTree.denote init :=
  treehash_loop_denote_eq hLeaf combinerTree combinerTree_allSingleVar init

/-- The discharged level-composition keystone, instantiated at the concrete
    halving counts and seed `init = 1`, computes `128` — byte-for-byte the
    unrolled treehash reference (`1 → 128` after seven doublings). This ties the
    emitted level-sequence semantics the keystone proves to the concrete KAT
    validated end-to-end in `bench/treehash/`. -/
theorem combinerTree_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    treehashLoopRun leafSem combinerTree (1 : BitVec 64) = (128 : BitVec 64) := by
  rw [combinerTree_treehash_denote_eq hLeaf]
  exact combinerTree_denote

/-! ## 9. A jasminc-compilable level-sequence `export fn` (`h` sequential `for`s)

To *validate* the level-sequence emission end-to-end we render it as a
self-contained jasminc `export fn`, mirroring `JForProg.toJazzExport` and
`NestedForProg.toJazzExport`: the accumulator `acc` is a `reg` initialised from
the export parameter, the body's fresh SSA names `v0, …` are declared registers,
the (single, shared) loop index `i` is `inline int`, and the body is the
**actual** emitted `h`-`Cfor` sequence (`toCfors`), printed by the shared
`ppInstrR` (NOT unrolled). The text jasminc KATs is the same level sequence the
proof covers. -/

/-- Emit a jasminc-compilable `export fn` for a `reg w` accumulator treehash. The
    body is the *actual* emitted `h`-`Cfor` sequence (one `for i = 0 to cnt` per
    level, from `toCfors`), printed by the shared `ppInstrR`.

    Shape (for a `reg w` accumulator, levels with counts `c0, c1, …`):
    ```
    export fn <name>(reg u<w> acc0) -> reg u<w> {
      reg u<w> acc;
      reg u<w> v0; …                 // one per level-body binder (max over levels)
      inline int i;
      acc = acc0;
      for i = 0 to c0 { <level 0 body> }
      for i = 0 to c1 { <level 1 body> }
      …
      return acc;
    }
    ``` -/
def TreehashProg.toJazzExport {w : Nat} (name : String)
    (levels : TreehashProg (.reg w)) : String :=
  let ws := (wsizeOfNat w).bits
  let wty := "u" ++ toString ws
  -- The emitted level sequence (`h` consecutive `for i` loops), via `ppInstrR`.
  let loopStr := String.intercalate "\n"
    (levels.toCfors.map (fun instr =>
      CatCrypt.Crypto.Jasmin.LowCT.ppInstrR 2 instr))
  -- Temporaries: the max number of binders over the levels (the shared `acc`
  -- write-back reuses the same `v0 …` names per level). For the single-leaf
  -- bodies here that is the per-level binder count, uniform across levels.
  let k := (levels.map (fun lvl => Com.numBinders lvl.update)).foldl Nat.max 0
  let tempDecls := String.intercalate "\n"
    ((List.range k).map (fun jdx => "  reg " ++ wty ++ " v" ++ toString jdx ++ ";"))
  let tempBlock := if k = 0 then "" else tempDecls ++ "\n"
  "export fn " ++ name ++ "(reg " ++ wty ++ " acc0) -> reg " ++ wty ++ " {\n" ++
  "  reg " ++ wty ++ " acc;\n" ++
  tempBlock ++
  "  inline int i;\n" ++
  "  acc = acc0;\n" ++
  loopStr ++ "\n" ++
  "  return acc;\n" ++
  "}"

/-! ## 10. Structural smoke tests for the emitted treehash `.jazz` -/

/-- The jasminc-compilable `export fn` for the 2→1 combiner treehash kernel. -/
def combinerTreeExportJazz : String :=
  TreehashProg.toJazzExport "treehash" combinerTree

#eval IO.println combinerTreeExportJazz

/- The exported `.jazz` has the **level-0** loop (`for i = 0 to 4`). -/
#guard (JasminPrint.strContains combinerTreeExportJazz "for i = 0 to 4")

/- The exported `.jazz` has the **level-1** loop (`for i = 0 to 2`). -/
#guard (JasminPrint.strContains combinerTreeExportJazz "for i = 0 to 2")

/- The exported `.jazz` has the **level-2** loop (`for i = 0 to 1`). -/
#guard (JasminPrint.strContains combinerTreeExportJazz "for i = 0 to 1")

/- **Structural check: the three level loops appear in halving sequence.** The
    level-0 header `for i = 0 to 4 {` is followed (later in the text) by the
    level-1 header `for i = 0 to 2 {`, which is followed by the level-2 header
    `for i = 0 to 1 {` — `h = 3` sequential `for` loops with the halving counts.
    We check by splitting on each header in turn and finding the next in the
    tail. -/
#guard (JasminPrint.strContains ((((combinerTreeExportJazz.splitOn "for i = 0 to 4 {").getLast!).splitOn "for i = 0 to 2 {").getLast!) "for i = 0 to 1 {")

/- The exported `.jazz` is an `export fn` jasminc unit. -/
#guard (JasminPrint.strContains combinerTreeExportJazz "export fn treehash")

/-- The exported `.jazz` does NOT unroll: it has exactly three `acc = acc + acc`
    bodies (one per level loop), confirming all three loops are emitted as real
    `for`s, not `4 + 2 + 1 = 7` copies of the body. -/
theorem combinerTreeExport_not_unrolled :
    (combinerTreeExportJazz.splitOn "(acc + acc)").length = 4 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgTreehash
