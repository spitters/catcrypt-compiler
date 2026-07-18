/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT
import CatCrypt.Crypto.SecureCompilation.UnifiedTrace

/-!
# Owned machine constant-time as an instance of robust-compilation (RHP)

This module connects our **owned** `JInstr`/`blockLeak` machine constant-time
results (`MachineConstantTime.lean`, `ConstantTimeCoverage.lean`, and the
source→machine bridges `LowCT{ToJInstr,Mem,For,Select}CT.lean`) to the
verified-compiler framework's **robust-hyperproperty-preservation (RHP)**
statement on the unified observable alphabet (`UnifiedTrace.lean`,
`RHPVerifiedMiddle.lean`).

## Why this matters

The framework's full-pipeline RHP theorem (`LowCTRHPFull.RHP_pipeline_full_labeled`)
delivers machine-level CT for the *general* Jasmin back-end only through the
**axiom-bridged** abstract predicate `X86Prog.isCT`, discharged by the cited
axiom `jasminc_preserves_ct` (Arranz-Olmos et al., arXiv 2511.11292). That
axiom is the right move for a back-end we do **not** own.

For the leaves our pipeline *emits itself* — the `JInstr 64` straight-line
subset — we do not need that axiom: the leakage model (`blockLeak`) is
concrete and the constant-time keystones (`blockLeak_state_independent`,
`blockLeak_pub_determined`) are fully proved. This file therefore provides the
**concrete, proved, owned-model instance** of the same robust-CT-preservation
the framework states abstractly, with **no** `jasminc_preserves_ct` in the
trust set.

## What is built

1. **Alphabet lift.** `MLeak.toEvent` embeds our machine leakage event into the
   framework's open `Event E LeakTy MemTy` alphabet at `LeakTy := MLeak`
   (the framework's documented extension point — no framework edit).
   `blockLeakU` is the unified-trace lift of `blockLeak`, mirroring
   `LeakTrace.toUnifiedTrace`.

2. **Per-block CT in the framework alphabet.** `lower{Seq,MemSeq,For,Select}_unifiedCT`
   recast the existing `_constant_time` theorems through `blockLeakU`.

3. **Robust (contextual) CT, two forms.**
   * **(a) RHP-shaped, identity back-translation** (`blockLeakU_RHP`): mirrors
     `RHPVerifiedMiddle.RHP_leakage_verified_middle` for our owned model —
     for every machine block, target context, and state there is a source
     context (the target itself) with matching `blockLeakU` lifts. Witness
     `⟨ctx, rfl⟩`. This shows the owned model satisfies the *same* RHP
     statement shape the framework proves.
   * **(b) Genuinely compositional robust CT** (`robust_CT`,
     `lowerSeq_robust_CT`, …): a compiled CT block linked (by `++`) with any
     direct-addressed context stays state-independent — CT is *preserved under
     linking*. This is the real robust-compilation content (not the trivial
     identity back-translation): it is proved from `blockLeak_append` +
     `allDirect_append` + `allDirect_constant_time`, with no axiom beyond the
     standard Lean kernel set.

4. **Equivalence.** `owned_CT_iff_RHP_blockLeakU` ties the denotational
   per-block CT (`blockLeak`-state-independence) to the framework-shaped
   `blockLeakU` form, both directions, for our owned `JInstr` model.

## Iris-freeness

The import closure is our `X86Backend` CT files + `UnifiedTrace`, all of
which are Iris-free. This module imports **no** Iris.

**0 sorries.** Standard Lean axioms only (`propext`, `Classical.choice`,
`Quot.sound`); in particular **no** `jasminc_preserves_ct`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT
open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open UCMonad.ITreeNUC

/-! ## §1. The alphabet lift: `MLeak` into the unified `Event` alphabet

The framework leaves the `LeakTy` slot of `Event E LeakTy MemTy` open precisely
so each stage can plug in its own side-channel observation type. The machine
back-end instantiates `LeakTy := MLeak`; this is the documented extension point
and requires no edit to `UnifiedTrace.lean`. Mirrors `LeakEvent.toEvent`. -/

/-- Embed a machine leakage event into the unified alphabet, at `LeakTy := MLeak`.
A branch decision and a memory access both become `.leak` events; the framework's
`.memOp`/`MemTy` slot is left untouched (our address-summary lives inside `MLeak`,
matching how `LeakEvent` already classifies `.sampleOp`/branch). -/
def MLeak.toEvent {E : EventSig} {MemTy : Type} (l : MLeak) : Event E MLeak MemTy :=
  .leak l

/-- The unified-trace lift of `blockLeak`: the machine leakage trace of running
`body` from `s`, mapped into the framework alphabet. Mirrors
`LeakTrace.toUnifiedTrace`. -/
def blockLeakU {E : EventSig} {MemTy : Type} {w : Nat}
    (s : JState w) (body : List (JInstr w)) : UnifiedTrace E MLeak MemTy :=
  (blockLeak s body).map (MLeak.toEvent (E := E) (MemTy := MemTy))

@[simp] theorem blockLeakU_nil {E : EventSig} {MemTy : Type} {w : Nat}
    (s : JState w) : blockLeakU (E := E) (MemTy := MemTy) s [] = [] := rfl

/-- If two `blockLeak`s agree, their unified lifts agree (`congrArg` of `.map`).
Mirrors the structure of `cprog_leakTrace_unified_constant`. -/
theorem blockLeakU_congr {E : EventSig} {MemTy : Type} {w : Nat}
    {s₁ s₂ : JState w} {body : List (JInstr w)}
    (h : blockLeak s₁ body = blockLeak s₂ body) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ body =
    blockLeakU (E := E) (MemTy := MemTy) s₂ body :=
  congrArg (fun t => t.map (MLeak.toEvent (E := E) (MemTy := MemTy))) h

/-! ## §2. Per-block constant-time in the framework alphabet

Each `_unifiedCT` is the existing `_constant_time` theorem viewed through
`blockLeakU`. The memory variant carries the `agreePub` premise of its
`blockLeak`-level source. -/

/-- The lowered straight-line scalar-arith block is CT in the unified alphabet:
its `blockLeakU` is the same from any two states. -/
theorem lowerSeq_unifiedCT {E : EventSig} {MemTy : Type}
    (ρ : RegMap) (ps : List ArithSrc) (s₁ s₂ : JState 64) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ (lowerSeq ρ ps) =
    blockLeakU (E := E) (MemTy := MemTy) s₂ (lowerSeq ρ ps) :=
  blockLeakU_congr (lowerSeq_constant_time ρ ps s₁ s₂)

/-- The lowered `for`-loop leaf is CT in the unified alphabet. -/
theorem lowerFor_unifiedCT {E : EventSig} {MemTy : Type}
    (ρ : RegMap) (f : ForSrc) (s₁ s₂ : JState 64) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ (lowerFor ρ f) =
    blockLeakU (E := E) (MemTy := MemTy) s₂ (lowerFor ρ f) :=
  blockLeakU_congr (lowerFor_constant_time ρ f s₁ s₂)

/-- The lowered branchless-`select` leaf is CT in the unified alphabet. -/
theorem lowerSelect_unifiedCT {E : EventSig} {MemTy : Type}
    (ρ : RegMap) (p : SelectSrc) (s₁ s₂ : JState 64) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ (lowerSelect ρ p) =
    blockLeakU (E := E) (MemTy := MemTy) s₂ (lowerSelect ρ p) :=
  blockLeakU_congr (lowerSelect_constant_time ρ p s₁ s₂)

/-- The lowered memory leaf is CT in the unified alphabet, **under** the
public-index premises: states that agree on the public registers produce the
same unified trace. Mirrors `lowerMemSeq_constant_time` lifted by `.map`. -/
theorem lowerMemSeq_unifiedCT {E : EventSig} {MemTy : Type}
    (pub : PubPred) (ρ : RegMap) (ms : List MemSrc)
    (h : ∀ m ∈ ms, m.ctPremise pub ρ) (s₁ s₂ : JState 64)
    (hag : agreePub pub s₁ s₂) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ (lowerMemSeq ρ ms) =
    blockLeakU (E := E) (MemTy := MemTy) s₂ (lowerMemSeq ρ ms) :=
  blockLeakU_congr (lowerMemSeq_constant_time pub ρ ms h s₁ s₂ hag)

/-! ## §3. `blockLeak` distributes over linking (`++`)

The linking combinator on machine leaves is list concatenation (the
straight-line back-end emits leaves and concatenates them). `blockLeak`
distributes over `++` with the state threaded through `runBlock` — the exact
machine-side analogue of the framework's `linkedLeakTrace = ... ++ ...`.
Mirrors `runBlock_append`. -/

/-- `blockLeak` distributes over concatenation, threading the state through
`runBlock` of the prefix. -/
theorem blockLeak_append {w : Nat} (s : JState w) (l₁ l₂ : List (JInstr w)) :
    blockLeak s (l₁ ++ l₂) = blockLeak s l₁ ++ blockLeak (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, blockLeak_cons, runBlock_cons, ih,
      List.append_assoc]

/-- The unified lift of linking is concatenation of the unified lifts. -/
theorem blockLeakU_append {E : EventSig} {MemTy : Type} {w : Nat}
    (s : JState w) (l₁ l₂ : List (JInstr w)) :
    blockLeakU (E := E) (MemTy := MemTy) s (l₁ ++ l₂) =
      blockLeakU (E := E) (MemTy := MemTy) s l₁ ++
      blockLeakU (E := E) (MemTy := MemTy) (runBlock s l₁) l₂ := by
  simp only [blockLeakU, blockLeak_append, List.map_append]

/-! ## §4. Form (a): RHP-shaped statement with identity back-translation

This mirrors `RHPVerifiedMiddle.RHP_leakage_verified_middle` exactly: a
machine-level context is itself a `List (JInstr 64)`, linking is `++`, and the
back-translation of a target context is the identity (the symmetric-adversary
structure — both sides are owned machine blocks). The witness is the target
context; the trace equality is `rfl`. Establishes that our owned model
satisfies the same RHP statement shape the framework proves on the verified
middle. -/

/-- A machine-level context is another straight-line leaf, linked by
concatenation. -/
abbrev MCtx : Type := List (JInstr 64)

/-- **Owned-model RHP (identity back-translation), unified alphabet.**

For every compiled machine `block`, every target context `ctx`, and every
initial state `s`, there is a source context — `ctx` itself — whose linked
unified leak trace equals the target's. Witness `⟨ctx, rfl⟩`; trace equality is
definitional. This is the machine-level analogue of
`RHP_leakage_verified_middle`. -/
theorem blockLeakU_RHP {E : EventSig} {MemTy : Type}
    (block ctx : MCtx) (s : JState 64) :
    ∃ srcCtx : MCtx,
      blockLeakU (E := E) (MemTy := MemTy) s (block ++ srcCtx) =
      blockLeakU (E := E) (MemTy := MemTy) s (block ++ ctx) :=
  ⟨ctx, rfl⟩

/-! ## §5. Form (b): genuinely compositional robust constant-time

The real robust-compilation content: a CT block linked with *any* direct-
addressed context stays constant-time. Unlike form (a) this is not the trivial
identity back-translation — it proves CT is **preserved under linking**, using
`blockLeak_append` and the additivity of `allDirect`. -/

/-- **Robust CT under linking.** If both `block` and `ctx` are `allDirect`, then
the linked leaf `block ++ ctx` is state-independent (constant-time): its machine
leakage trace is the same from any two initial states. CT is preserved under
linking with any direct-addressed context. -/
theorem robust_CT (block ctx : List (JInstr 64))
    (hb : allDirect block = true) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (block ++ ctx) = blockLeak s₂ (block ++ ctx) :=
  allDirect_constant_time (block ++ ctx)
    (by rw [allDirect_append, hb, hc, Bool.and_self]) s₁ s₂

/-- The unified-alphabet form of `robust_CT`. -/
theorem robust_unifiedCT {E : EventSig} {MemTy : Type}
    (block ctx : List (JInstr 64))
    (hb : allDirect block = true) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeakU (E := E) (MemTy := MemTy) s₁ (block ++ ctx) =
    blockLeakU (E := E) (MemTy := MemTy) s₂ (block ++ ctx) :=
  blockLeakU_congr (robust_CT block ctx hb hc s₁ s₂)

/-- **`lowerSeq` robust CT.** The compiled straight-line scalar block, linked
with any direct-addressed machine context, stays constant-time. The block's CT
comes from `lowerSeq_allDirect`; the context's from its `allDirect` hypothesis.
This is the compiler-correctness reading: code we emit remains CT against any
direct-addressed surrounding leaf. -/
theorem lowerSeq_robust_CT (ρ : RegMap) (ps : List ArithSrc)
    (ctx : List (JInstr 64)) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSeq ρ ps ++ ctx) = blockLeak s₂ (lowerSeq ρ ps ++ ctx) :=
  robust_CT (lowerSeq ρ ps) ctx (lowerSeq_allDirect ρ ps) hc s₁ s₂

/-- **`lowerFor` robust CT.** The compiled `for`-loop leaf stays CT linked with
any direct-addressed context. -/
theorem lowerFor_robust_CT (ρ : RegMap) (f : ForSrc)
    (ctx : List (JInstr 64)) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerFor ρ f ++ ctx) = blockLeak s₂ (lowerFor ρ f ++ ctx) :=
  robust_CT (lowerFor ρ f) ctx (lowerFor_allDirect ρ f) hc s₁ s₂

/-- **`lowerSelect` robust CT.** The compiled branchless-`select` leaf stays CT
linked with any direct-addressed context. -/
theorem lowerSelect_robust_CT (ρ : RegMap) (p : SelectSrc)
    (ctx : List (JInstr 64)) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSelect ρ p ++ ctx) = blockLeak s₂ (lowerSelect ρ p ++ ctx) :=
  robust_CT (lowerSelect ρ p) ctx (lowerSelect_allDirect ρ p) hc s₁ s₂

/-! ## §6. The equivalence: owned per-block CT ⇔ framework-shaped robust CT

For our owned `JInstr` model the denotational per-block CT
(`blockLeak`-state-independence) and the framework-shaped unified robust-CT
(`blockLeakU` agreement) say the same thing — the lift `MLeak.toEvent` is
injective on the leak constructor, so the `.map` is injective and the two forms
are inter-derivable. We give the easy direction unconditionally and the converse
via injectivity of `MLeak.toEvent`. -/

/-- `MLeak.toEvent` is injective: distinct machine leaks map to distinct unified
events. (Both land in the `.leak` constructor, which is injective.) -/
theorem MLeak.toEvent_injective {E : EventSig} {MemTy : Type} :
    Function.Injective (MLeak.toEvent (E := E) (MemTy := MemTy)) := by
  intro a b h
  simpa [MLeak.toEvent] using h

/-- **Equivalence of the two CT formulations for the owned model.**

For any machine block, denotational per-block CT (the leak trace is the same
from any two states) is *equivalent* to its unified-alphabet form
(`blockLeakU` agreement). Forward is `blockLeakU_congr`; backward uses
injectivity of the `.map` of `MLeak.toEvent`. This is the precise sense in
which our owned `blockLeak` CT *is* an instance of the framework's
`UnifiedTrace`-based robust-CT-preservation. -/
theorem owned_CT_iff_RHP_blockLeakU {E : EventSig} {MemTy : Type}
    {w : Nat} (s₁ s₂ : JState w) (body : List (JInstr w)) :
    blockLeak s₁ body = blockLeak s₂ body ↔
    blockLeakU (E := E) (MemTy := MemTy) s₁ body =
    blockLeakU (E := E) (MemTy := MemTy) s₂ body := by
  constructor
  · exact blockLeakU_congr
  · intro h
    exact List.map_injective_iff.mpr (MLeak.toEvent_injective (E := E) (MemTy := MemTy)) h

/-! ## §7. The headline owned-model robust-CT theorem

The single statement bundling the framework connection: for any compiled CT
block linked with any direct-addressed context, the owned model satisfies *both*
the RHP-shaped identity-back-translation statement (form (a)) and genuine
compositional CT preservation (form (b)) — in the framework's unified alphabet,
with no `jasminc_preserves_ct`. -/

/-- **Owned-model robust constant-time, framework-connected.**

For any direct-addressed compiled `block` and direct-addressed context `ctx`:

* (a) RHP-shaped: a source context (`ctx` itself) reproduces the target's linked
  unified trace; and
* (b) compositional: the linked leaf `block ++ ctx` is constant-time in the
  unified alphabet (same trace from any two states).

This is the concrete, proved, owned-model instance of the verified compiler's
robust-CT-preservation — replacing the cited `jasminc_preserves_ct` axiom for
the leaves we emit ourselves. -/
theorem owned_robust_CT_framework
    {E : EventSig} {MemTy : Type}
    (block ctx : MCtx)
    (hb : allDirect block = true) (hc : allDirect ctx = true)
    (s : JState 64) :
    (∃ srcCtx : MCtx,
      blockLeakU (E := E) (MemTy := MemTy) s (block ++ srcCtx) =
      blockLeakU (E := E) (MemTy := MemTy) s (block ++ ctx)) ∧
    (∀ s' : JState 64,
      blockLeakU (E := E) (MemTy := MemTy) s (block ++ ctx) =
      blockLeakU (E := E) (MemTy := MemTy) s' (block ++ ctx)) :=
  ⟨blockLeakU_RHP (E := E) (MemTy := MemTy) block ctx s,
   fun s' => robust_unifiedCT (E := E) (MemTy := MemTy) block ctx hb hc s s'⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT
