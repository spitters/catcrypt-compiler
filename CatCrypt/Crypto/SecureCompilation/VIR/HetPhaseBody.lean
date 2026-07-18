/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MultiPhaseBody

/-!
# Heterogeneous multi-phase whole-protocol body: a TYPED sequence of phases whose
# live state changes type between phases, with composed run = the chained
# semantics

`MultiPhaseBody.lean` composes a `List (Phase accTy)` where every phase is a
*self-map* of one fixed accumulator type (`run sem : ⟦accTy⟧ → ⟦accTy⟧`). Its
flagged next step: a phase whose live set grows/shrinks (a typed seam
`accTy₁ → accTy₂`) needs a **dependent / heterogeneous** phase list — a
length-indexed dependent fold.

Real protocols change their live set between phases: a key schedule **expands** a
seed into round keys (`seed → keySchedule`), a sponge **contracts** a wide state
into a digest (`state → digest`), an AEAD packs several registers into a wider
SIMD word. The composed object is no longer a `List` of self-maps but a **typed
chain** `phase₁ : a → b`, `phase₂ : b → c`, … whose adjacent endpoints must
agree — exactly a GADT-style heterogeneous sequence.

This file generalises `Phase accTy` (a self-map) to `HetPhase a b` (a typed
transform `⟦a⟧ → ⟦b⟧`), and the `List (Phase accTy)` to a GADT-indexed chain
`HetChain a b` (`nil : HetChain a a`, `cons : HetPhase a b → HetChain b c →
HetChain a c`). The composed run / semantics are defined by structural recursion
on the chain, and the composed soundness `chainRun = chainSem` is proved by
induction on the chain — the head phase's `sound` rewrites the first step, the
tail closes by the inductive hypothesis on the intermediate value the head
produced. Every per-phase soundness is reused verbatim; the new content is
threading per-phase soundness through a *type-changing* dependent fold.

## The model (reuse, not rebuild)

A **heterogeneous phase** `HetPhase a b` is a typed transform together with its
own already-discharged soundness:

* `run  : ⟦a⟧ → ⟦b⟧` — the emitted evaluator run as a typed transform.
* `sem  : ⟦a⟧ → ⟦b⟧` — the reference semantics.
* `sound : run = sem` — the per-phase soundness, supplied at construction by a
  landed keystone.

Two smart constructors discharge `sound` with no new proof obligation:

* `straightHetPhase` — the **genuinely heterogeneous** case: a type-changing
  straight-line block `com : Com jasminDialect [a] b` (input type `a`, output
  type `b`, `a ≠ b` in general). `sound` is
  `WholeFnLowering.lowerComToProg_sem_eq'` instantiated at the singleton
  valuation `V = .cons init .nil`. This is the very lowering used for `smokeProg`
  (`[reg 32, reg 32] → reg 64`), where input and output types already differ.
* `loopHetPhase` — a counted-loop phase lifted into the chain as an `a → a`
  transform (a loop preserves the accumulator type, so a loop phase is the
  *diagonal* `HetPhase a a`). `sound` is `LoopLowering.loopN_lower_denote_iterate`.

A **protocol** is then a `HetChain a b`; its composed run / semantics are defined
by recursion on the chain, and the composed soundness is `chainRun_eq` by
induction on the chain.

## What is reused vs newly proved

* **Reused verbatim** (no new proof obligation): every per-phase soundness —
  `lowerComToProg_sem_eq'`, `loopN_lower_denote_iterate`. The smart constructors
  thread them into the `sound` field. The straight-line constructor reuses
  `MultiPhaseBody`'s machinery directly (it is the *same* `lowerComToProg_sem_eq'`
  edge, now used at a type-changing context `[a] → b`).
* **Newly proved**: `HetPhase a b` (the typed phase), the GADT `HetChain a b`,
  `chainRun`/`chainSem` (recursion on the chain), and `chainRun_eq` (the composed
  soundness, by induction on the GADT — the genuinely new content: threading
  per-phase soundness through a type-changing dependent chain).

## Conditioned scope (honest)

Each phase carries its own `sound`, so the carried hypotheses are exactly the
union of the per-phase hypotheses: every phase needs `LeafAgrees leafSem`, and
each straight-line / loop phase additionally needs its body `StraightLine`. These
are supplied once at construction and never re-incurred by the chain induction.

It does **not** cover: data-dependent phase **selection** (the chain is fixed,
not chosen by a runtime predicate — that is the `if`/branch layer); **calls
between phases as a single fused control-flow graph** (this composes the phases'
emitted runs at the meta level over a shared *value* of the intermediate type,
exactly as `MultiPhaseBody`/`WholeProtocolBody` compose phases — the `extCall`
leaf stays opaque under `LeafAgrees`, it is not a fused CFG with a real `call`
instruction threading the intermediate type through registers). Those are the
remaining whole-protocol-body work. What this file *does* add over
`MultiPhaseBody` is the typed seam: the intermediate value changes type between
phases, so the chain is dependent rather than a homogeneous `List`.

0 sorries; the only carried hypotheses are `LeafAgrees` and the per-phase
`StraightLine` witnesses, the same edges carried throughout the emit theory.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.HetPhaseBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody

/-! ## 1. A single heterogeneous phase: a sound typed transform

A `HetPhase a b` is a typed transform `⟦a⟧ → ⟦b⟧` — its live state may change
type from `a` (incoming) to `b` (outgoing). It bundles the emitted evaluator
run, the reference semantics, and a proof that they agree. The proof is
discharged at construction by a landed keystone, so a het-phase is *by
construction* a verified type-changing transform. The homogeneous `Phase accTy`
of `MultiPhaseBody` is the diagonal case `HetPhase accTy accTy`. -/

/-- **A single verified heterogeneous phase.** A typed transform `⟦a⟧ → ⟦b⟧` (the
    live state changes type from `a` to `b`) packaging the emitted evaluator
    `run`, the reference `sem`antics, and the per-phase soundness
    `sound : run = sem` (discharged at construction by a landed keystone). The
    unit of composition for a type-changing multi-phase protocol body. -/
structure HetPhase (a b : JasminTy) where
  /-- The emitted evaluator run, as a typed transform `⟦a⟧ → ⟦b⟧`. -/
  run : ⟦a⟧ → ⟦b⟧
  /-- The reference semantics, as a typed transform `⟦a⟧ → ⟦b⟧`. -/
  sem : ⟦a⟧ → ⟦b⟧
  /-- The per-phase soundness: the emitted run equals the reference semantics.
      Supplied by an existing keystone at construction. -/
  sound : run = sem

/-! ## 2. Smart constructors — each discharges `sound` from a landed keystone -/

/-- **A type-changing straight-line block phase (the genuinely heterogeneous
    case).** `straightHetPhase hLeaf com hSL` runs the straight-line block
    `com : Com jasminDialect [a] b` (input type `a`, output type `b`, in general
    `a ≠ b`) over the incoming value; `sem` is its `Com.denote`. `sound` is
    `WholeFnLowering.lowerComToProg_sem_eq'` instantiated at the singleton
    valuation `V = .cons init .nil` (no new obligation — the *same* edge
    `MultiPhaseBody.straightPhase` uses, now at a type-changing context). Requires
    the block to be `StraightLine`. -/
def straightHetPhase {a b : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (com : Com jasminDialect [a] b)
    (hSL : StraightLine com) : HetPhase a b where
  run := fun init => runProg leafSem com (.cons init .nil)
  sem := fun init => com.denote (.cons init .nil)
  sound := by
    funext init
    exact lowerComToProg_sem_eq' hLeaf com hSL (.cons init .nil)

/-- **A counted-loop phase, lifted into the chain as the diagonal `a → a`.** A
    counted loop preserves the accumulator type, so `loopHetPhase hLeaf n body` is
    a `HetPhase a a`: it runs the counted loop `loopN n body` over the incoming
    accumulator; its `sem` is the `n`-fold body denotation. `sound` is
    `LoopLowering.loopN_lower_denote_iterate` (no new obligation). This is the
    `HetPhase`-valued image of `MultiPhaseBody.loopPhase`. -/
def loopHetPhase {a : JasminTy} {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) (body : LoopBody a) : HetPhase a a where
  run := fun init =>
    loopRun (loopN n body) (bodyStepRun leafSem (loopN n body)) init
  sem := fun init => (fun acc => body.denote (.cons acc .nil))^[n] init
  sound := by
    funext init
    exact loopN_lower_denote_iterate hLeaf n body init

/-! ## 3. The typed chain: a GADT-indexed dependent sequence of het-phases

A protocol is a `HetChain a b`: a typed sequence of het-phases whose adjacent
endpoints agree. `nil` is the identity chain `a → a`; `cons` prepends a head
phase `a → b` onto a tail chain `b → c`, producing a chain `a → c`. The index
types enforce the seam at the *type* level: a phase that outputs `b` can only be
followed by a chain that consumes `b`. -/

/-- **A typed chain of heterogeneous phases** (`HetChain a b`). The GADT-style
    heterogeneous sequence: `nil` is the identity chain (`a → a`); `cons` prepends
    a head het-phase `HetPhase a b` onto a tail `HetChain b c` to form a chain
    `HetChain a c`. The indices thread the changing live-state type through the
    whole protocol body — the dependent/typed seam `MultiPhaseBody`'s homogeneous
    `List (Phase accTy)` cannot express. -/
inductive HetChain : JasminTy → JasminTy → Type where
  /-- The empty chain — the identity transform `a → a`. -/
  | nil {a : JasminTy} : HetChain a a
  /-- Prepend a head phase `a → b` onto a tail chain `b → c`, giving `a → c`. -/
  | cons {a b c : JasminTy} (p : HetPhase a b) (rest : HetChain b c) :
      HetChain a c

/-- **The composed emitted run.** Thread the chain's phases' `run`s
    left-to-right: `nil` is the identity; `cons p rest` runs the head `p.run`,
    then the tail chain over the result `p.run init` (whose type is `p`'s output
    type `b`). The whole type-changing protocol-body run, by structural recursion
    on the chain. -/
def chainRun : {a b : JasminTy} → HetChain a b → ⟦a⟧ → ⟦b⟧
  | _, _, .nil, x => x
  | _, _, .cons p rest, x => chainRun rest (p.run x)

/-- **The composed reference semantics.** Thread the chain's phases' `sem`antics
    left-to-right — the type-changing analogue of the function composition
    `phaseₖ.sem ∘ … ∘ phase₁.sem`, where each intermediate value carries the next
    phase's input type. The ground truth the composed run must match. -/
def chainSem : {a b : JasminTy} → HetChain a b → ⟦a⟧ → ⟦b⟧
  | _, _, .nil, x => x
  | _, _, .cons p rest, x => chainSem rest (p.sem x)

/-! ## 4. The composed soundness — by induction on the GADT chain -/

/-- **Composed heterogeneous-phase denote-correctness.** The composed emitted run
    of a typed chain of phases equals the composed reference semantics — the
    type-changing chained composition of the phases' `sem`antics applied to the
    initial value. By induction on the GADT chain: `nil` is `rfl`; for
    `cons p rest`, the head phase's `run = sem` (its `sound` field) rewrites the
    first step, and the tail closes by the inductive hypothesis on the
    intermediate value `p.sem init` (whose type is the head's output type). Every
    per-phase soundness is reused verbatim; threading it through a *type-changing*
    dependent chain is the new content. No global hypothesis: each phase already
    carries its own (`LeafAgrees` + `StraightLine`). -/
theorem chainRun_eq : {a b : JasminTy} → (ch : HetChain a b) → (init : ⟦a⟧) →
    chainRun ch init = chainSem ch init
  | _, _, .nil, _ => rfl
  | _, _, .cons p rest, init => by
      show chainRun rest (p.run init) = chainSem rest (p.sem init)
      rw [p.sound]
      exact chainRun_eq rest (p.sem init)

/-- **Composition form.** The composed semantics of `cons p rest` threads
    `p.sem init` (of `p`'s output type) into the rest — the explicit
    "type-changing chained composition of the phases' semantics" reading. A
    `simp`-normal restatement of `chainSem` on a `cons`. -/
theorem chainSem_cons {a b c : JasminTy} (p : HetPhase a b) (rest : HetChain b c)
    (init : ⟦a⟧) :
    chainSem (.cons p rest) init = chainSem rest (p.sem init) := rfl

/-! ## 5. Worked example: a 2-phase chain WITH A TYPE CHANGE,
# `widen (reg 64 → reg 128); double-loop (reg 128 → reg 128)`

The validating heterogeneous kernel: a straight-line **widen** phase
`reg 64 → reg 128` (a single `castW 64 128`, the seed-to-wider-state expansion),
then a **doubling loop** `reg 128 → reg 128` (`acc := acc + acc`, `n` times) over
the *widened* state. The first phase genuinely changes the live-state type
(`reg 64 ⇒ reg 128`); the second is the diagonal loop. The composed semantics is
`double^[n] (zeroExtend 128 init)`. -/

/-- The straight-line **widen** block `reg 64 → reg 128`: a single `castW 64 128`
    (zero-extend) over the singleton context `[reg 64]`, returning `reg 128`. The
    simplest genuine *type-changing* straight-line `Com` — input type `reg 64`,
    output type `reg 128`. Denotes `x ↦ x.zeroExtend 128`. -/
def widenBlock : Com jasminDialect [JasminTy.reg 64] (.reg 128) :=
  .var (.mk (.castW 64 128) rfl (.cons .here .nil))
    (.ret .here)

/-- `widenBlock` is straight-line (its lone binder is a `castW`, not the aliasing
    `stackStore`). -/
theorem widenBlock_straightLine : StraightLine widenBlock := by
  refine ⟨fun w n h => ?_, trivial⟩
  exact absurd h (by simp)

/-- `widenBlock.denote ⟨x⟩ = x.zeroExtend 128`. -/
@[simp] theorem widenBlock_denote (x : BitVec 64) :
    widenBlock.denote (.cons x .nil) = x.zeroExtend 128 := rfl

/-- The doubling body `acc ↦ acc + acc` at width 128 (the `reg 128` analogue of
    `LoopLowering.doubleBody`). One `regArith add 128` on the accumulator twice. -/
def doubleBody128 : LoopBody (.reg 128) :=
  .mk (.regArith .add 128) rfl (.cons .here (.cons .here .nil))

/-- **The worked heterogeneous 2-phase protocol** (a `HetChain (reg 64) (reg 128)`):
    `straightHetPhase widenBlock` (the type change `reg 64 → reg 128`), then
    `loopHetPhase n doubleBody128` (the diagonal `reg 128 → reg 128` loop). The
    live-state type changes between the two phases — what the homogeneous
    `List (Phase accTy)` of `MultiPhaseBody` cannot express. -/
def widenThenDouble {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) (n : Nat) :
    HetChain (.reg 64) (.reg 128) :=
  .cons (straightHetPhase hLeaf widenBlock widenBlock_straightLine)
    (.cons (loopHetPhase hLeaf n doubleBody128) .nil)

/-- **Worked example (composition form).** The composed run of the heterogeneous
    2-phase protocol equals `double^[n] (init.zeroExtend 128)` — the widen phase
    expands `reg 64 → reg 128`, then the loop doubles `n` times at width 128.
    Instance of `chainRun_eq`, exercising a genuine type change across the seam. -/
theorem widenThenDouble_run_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (n : Nat) (init : BitVec 64) :
    chainRun (widenThenDouble hLeaf n) init
      = (fun a => a + a)^[n] (init.zeroExtend 128) := by
  rw [chainRun_eq]
  unfold widenThenDouble chainSem
  simp only [straightHetPhase, loopHetPhase]
  rfl

/-- **Worked example (concrete KAT).** On seed `init = 5` with `n = 3`: the widen
    phase zero-extends `5 : reg 64 → 5 : reg 128`, then the loop doubles thrice
    `5 → 10 → 20 → 40`, i.e. `40`. Ties the heterogeneous-chain composition
    keystone to a concrete value across a real type change `reg 64 → reg 128`. -/
theorem widenThenDouble_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    chainRun (widenThenDouble hLeaf 3) (5 : BitVec 64) = (40 : BitVec 128) := by
  rw [widenThenDouble_run_eq hLeaf]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.HetPhaseBody
