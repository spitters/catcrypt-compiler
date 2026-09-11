/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.CompilerSecurity.DialectLeakRefinement
public import CatCrypt.Crypto.CompilerSecurity.DialectLeakRefinement

/-!
# Dialect → jasmin → x86 leak-refinement, extended to the direct-memory fragment

`DialectLeakRefinement.lean` closed the dialect → jasmin → x86 leak-refinement
**chain** on the *owned scalar-arith* fragment: the jasmin → x86 leg
(`blockLeak (lowerSeq ρ ps)` state-independent) was proved only for the
register-only `lowerSeq` leaf (a `List ArithSrc`, all `IsDirect`, no memory op).
Its "precise remaining edge" named the general op-set jasmin → x86 leak
preservation — `stackLoad`/`stackStore`/multi-result/vector — as routing through
the un-owned backend's `jasminc_preserves_ct`.

This file closes the next genuine slice of that edge: the **direct /
public-addressed memory fragment** — `stackLoad` / `stackStore` at a
compile-time-constant offset (the `loadMem`/`storeMem` reg-ptr-ABI ops, all
`IsDirect`). It does so **directly on the owned/concrete `blockLeak` model**, the
same way the scalar leg does — *without* `jasminc_preserves_ct`.

## What this file delivers

* **§1 A direct-memory leaf model `MemOp`** — a `stackLoad dst base off` /
  `stackStore base off src` at a compile-time-**constant** `off` (the `IsDirect`
  reg-ptr-ABI memory ops), and its lowering `lowerMem : MemOp → JInstr 64` to
  exactly `loadMem` / `storeMem`. A block of them lowers via `lowerMemSeq`.

* **§2 Direct-memory leak preservation (the keystone), `jasminc_preserves_ct`-free.**
  Every lowered `MemOp` is `IsDirect` (`lowerMem_isDirect`), so its concrete x86
  `blockLeak` is **state-independent**: the leaked address `(base, off)` is a
  compile-time constant, carrying no register value — `lowerMemSeq_constant_time`,
  proved through `MachineConstantTime.blockLeak_state_independent`
  (via `ConstantTimeCoverage.allDirect_constant_time`), exactly as the scalar leg,
  with no appeal to the opaque backend.

* **§3 A mixed scalar-ALU + direct-memory leaf `MixedOp`** — the realistic shape
  of an emitted field/bignum leaf (load operands, fold with scalar ALU, store the
  result back). Its lowering `lowerMixedSeq` is all-`IsDirect`, so the same
  keystone gives `lowerMixedSeq_constant_time`, again `jasminc_preserves_ct`-free.
  This is the fragment that strictly **extends** the scalar-only `lowerSeq` leg.

* **§4 The extended chain.** Re-running the `DialectLeakRefinement` composition
  with the direct-memory realization predicate `RealizesMem` /
  `RealizesMixed`, `dialect_jasmin_x86_chain_mem` /
  `dialect_jasmin_x86_chain_mixed` tie the abstract dialect leak trace
  (`leakTraceCom`), its length-preserving jasmin image (`leakTraceJ`,
  `leakTraceJ_length_refines`), and the concrete x86 `blockLeak` for programs
  that emit direct `stackLoad`/`stackStore` in addition to scalar ALU — closing
  the chain on the direct-memory fragment.

* **§5 Sharp honesty: the register-indexed memory op is provably NOT CT.** The
  reason the register-indexed (secret-index) ops are **excluded** from this
  extension is not a missing proof but an inherent property: a register-indexed
  store leaks the index *value* into its address trace. We re-expose
  `MachineConstantTime.nonCT_storeMemIdx_leaks_value` as
  `regIndexed_provably_not_CT` to state precisely that the excluded case is
  *provably not constant-time*, distinct from "not yet proved".

## Scope

The chain that closes here, **axiom-free of `jasminc_preserves_ct`**, is the
**direct / public-addressed memory fragment plus scalar ALU**: the leaves whose
every instruction is

  scalar ALU (`mov`/`add`/`and`/`xor`/`imul`/`sub`/`sbb`/`adc`/`mulx`/…)
  or a **direct** `loadMem`/`storeMem` at a compile-time-constant displacement.

On exactly that fragment:

* (dialect → jasmin) the leak trace length is preserved by the front
  (`leakTraceJ_length_refines`, reused from `DialectLeakRefinement`), and the
  syntax-only state-independence transports down — proved there, no axiom;
* (jasmin → x86) the concrete `blockLeak (lowerMemSeq …)` /
  `blockLeak (lowerMixedSeq …)` is state-independent and branch-free — proved
  **here**, directly on the owned concrete `blockLeak` model
  (`MachineConstantTime`/`ConstantTimeCoverage`), with **no
  `jasminc_preserves_ct`**.

So `DialectLeakRefinement`'s owned scalar-arith leg is extended one op-class
wider: direct memory loads/stores now close at the concrete x86 machine level.

### Which ops close, which are excluded by design, which are not yet modeled

* **Close here (new):** direct `stackLoad`/`stackStore` at a constant offset
  (`loadMem`/`storeMem`), alone or mixed with scalar ALU. State-independent
  `blockLeak`, branch-free, `jasminc_preserves_ct`-free.
* **Excluded *by design* — provably not CT (not a gap):** the register-indexed
  (secret-index) memory ops `loadMemIdx`/`storeMemIdx`. A secret-indexed load
  *is* a leak: its address trace is a function of the index register's value
  (`regIndexed_provably_not_CT` / `nonCT_storeMemIdx_leaks_value`). These are
  correctly outside `IsDirect`. The honest dual is *public*-indexed addressing
  (a public loop counter), which **is** CT in the standard sense — covered by
  `MachineConstantTime.blockLeak_pub_determined`; we expose the worked
  public-indexed leaf below as `pubIndexed_is_CT`. So the boundary is exactly
  secret-vs-public index, not direct-vs-indexed in general.
* **Not yet modeled (the precise remaining edge):** multi-result `callN` /
  vector (`vpackZMM`/SIMD) ops, whose effective addressing and leakage are not
  yet given a `blockLeak` instruction case in the scalar `JInstr 64` model; and
  the general (non-`MemOp`/`MixedOp`-shaped) dialect `stackLoad`/`stackStore`
  whose offset is not a syntactic constant. These remain on the
  `DialectLeakRefinement` edge and are *not* claimed here.

## Axioms

§1–§4 are pure reuse of `MachineConstantTime.blockLeak_state_independent` /
`ConstantTimeCoverage.allDirect_constant_time` (structural inductions on the
emitted block) and the `DialectLeakRefinement` §1/§2 length-refinement. **No
`jasminc_preserves_ct`** is threaded — the direct-memory x86 leg is the concrete
`blockLeak` model, not the opaque `X86Prog.isCT`. §5 reuses
`nonCT_storeMemIdx_leaks_value` (whose only non-standard axioms are the
`native_decide` pins `propext`/`Quot.sound`/`Lean.ofReduceBool`).

**0 sorries.** Standard axioms only.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinementMem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace (Com.leakTrace)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinement
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

set_option autoImplicit false

/-! ## §1. The direct-memory leaf model

A `MemOp` is a direct (base + compile-time-constant displacement) memory access —
the `stackLoad` / `stackStore` at a constant offset that lower to the reg-ptr-ABI
`loadMem` / `storeMem`. The constant offset is what makes these `IsDirect`: the
leaked address `(base, off)` is fixed by the program text, never read out of a
register. The register-indexed `loadMemIdx`/`storeMemIdx` are *not* `MemOp`s — by
design (see §5). -/

/-- A direct (constant-offset) memory operation: either a load
    `dst := [base + off]` or a store `[base + off] := src`. The displacement
    `off` is a compile-time constant, so the access is `IsDirect`. This is the
    direct `stackLoad`/`stackStore` fragment; the register-indexed ops are
    deliberately not representable. -/
inductive MemOp where
  /-- Direct load `dst := [base + off]` — lowers to `loadMem`. -/
  | load (dst base : String) (off : Int)
  /-- Direct store `[base + off] := src` — lowers to `storeMem`. -/
  | store (base : String) (off : Int) (src : String)
  deriving Repr

/-- **The direct-memory lowering.** A `MemOp` lowers to exactly one reg-ptr-ABI
    `JInstr 64`: `load` to `loadMem`, `store` to `storeMem`. Both use direct
    base+constant-displacement addressing. -/
def lowerMem : MemOp → JInstr 64
  | .load dst base off  => .loadMem dst base off
  | .store base off src => .storeMem base off (.reg src)

/-- The basic-block lowering of a straight-line list of direct-memory ops. -/
def lowerMemSeq (ms : List MemOp) : List (JInstr 64) :=
  ms.map lowerMem

@[simp] theorem lowerMemSeq_nil : lowerMemSeq [] = [] := rfl

@[simp] theorem lowerMemSeq_cons (m : MemOp) (ms : List MemOp) :
    lowerMemSeq (m :: ms) = lowerMem m :: lowerMemSeq ms := rfl

/-! ## §2. Direct-memory leak preservation, `jasminc_preserves_ct`-free

Each `lowerMem m` is one of `loadMem`/`storeMem`, both `IsDirect` (the only
non-`IsDirect` ops are `loadMemIdx`/`storeMemIdx`, which `MemOp` cannot produce).
So the whole `lowerMemSeq` block is `allDirect`, and its concrete x86 `blockLeak`
is state-independent by the machine keystone — exactly as the scalar leg, with no
appeal to the opaque backend. -/

/-- A single lowered `MemOp` is `IsDirect`: it is a `loadMem`/`storeMem` at a
    compile-time-constant displacement, never a register-indexed op. -/
theorem lowerMem_isDirect (m : MemOp) : IsDirect (lowerMem m) := by
  cases m <;> exact True.intro

/-- The whole direct-memory block passes the decidable `allDirect` check: every
    emitted instruction is a direct `loadMem`/`storeMem`. -/
theorem lowerMemSeq_allDirect (ms : List MemOp) :
    allDirect (lowerMemSeq ms) = true := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      rw [lowerMemSeq_cons, allDirect, List.all_cons, ← allDirect, ih,
          Bool.and_true, decide_eq_true_eq]
      exact lowerMem_isDirect m

/-- **Direct-memory leak preservation (the keystone), `jasminc_preserves_ct`-free.**
    A straight-line block of direct `stackLoad`/`stackStore` ops produces the
    **same** concrete x86 machine leakage trace from any two initial states: the
    leaked address `(base, off)` of every access is a compile-time constant, so
    the observable cache-line sequence carries no register-value information. This
    is a *genuine* `IsDirect`-gated theorem (not a vacuity — `blockLeak` reads the
    running state and would expose a register-indexed address), proved directly on
    the owned concrete `blockLeak` model via `allDirect_constant_time`, with **no
    `jasminc_preserves_ct`**. -/
theorem lowerMemSeq_constant_time (ms : List MemOp) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerMemSeq ms) = blockLeak s₂ (lowerMemSeq ms) :=
  allDirect_constant_time (lowerMemSeq ms) (lowerMemSeq_allDirect ms) s₁ s₂

/-- The direct-memory block has no control-flow (branch) leak: it emits no
    conditional jump, so the branch channel is empty regardless of state. -/
theorem lowerMemSeq_no_branch (ms : List MemOp) (s : JState 64) :
    (blockLeak s (lowerMemSeq ms)).filter MLeak.isBranch = [] :=
  allDirect_no_branch (lowerMemSeq ms) s

/-! ## §3. Mixed scalar-ALU + direct-memory leaf

A realistic emitted field/bignum leaf interleaves direct memory ops (load
operands, store results) with scalar ALU (the fold). `MixedOp` is either a
scalar-arith statement (`ArithSrc`, the `lowerArith` fragment from the scalar
leg) or a direct `MemOp`. Its lowering is all-`IsDirect`, so the same keystone
applies — this is the fragment that strictly extends the scalar-only
`lowerSeq`. -/

/-- A mixed leaf statement: a scalar-arith assignment (`ArithSrc`) or a direct
    memory op (`MemOp`). -/
inductive MixedOp where
  /-- A scalar-arith statement, lowered by `lowerArith`. -/
  | arith (p : ArithSrc)
  /-- A direct memory op, lowered by `lowerMem`. -/
  | mem (m : MemOp)

/-- The lowering of one mixed statement: scalar-arith via `lowerArith` (a
    `mov; op` pair), direct memory via `lowerMem` (one `loadMem`/`storeMem`). -/
def lowerMixed (ρ : RegMap) : MixedOp → List (JInstr 64)
  | .arith p => lowerArith ρ p
  | .mem m   => [lowerMem m]

/-- The basic-block lowering of a mixed scalar-ALU + direct-memory leaf. -/
def lowerMixedSeq (ρ : RegMap) (xs : List MixedOp) : List (JInstr 64) :=
  xs.flatMap (lowerMixed ρ)

@[simp] theorem lowerMixedSeq_nil (ρ : RegMap) : lowerMixedSeq ρ [] = [] := rfl

@[simp] theorem lowerMixedSeq_cons (ρ : RegMap) (x : MixedOp) (xs : List MixedOp) :
    lowerMixedSeq ρ (x :: xs) = lowerMixed ρ x ++ lowerMixedSeq ρ xs := by
  simp [lowerMixedSeq, List.flatMap_cons]

/-- One mixed statement lowers to an all-`IsDirect` block: the scalar-arith arm is
    memory-free (`lowerArith_allDirect`), the memory arm is a direct
    `loadMem`/`storeMem` (`lowerMem_isDirect`). -/
theorem lowerMixed_allDirect (ρ : RegMap) (x : MixedOp) :
    allDirect (lowerMixed ρ x) = true := by
  cases x with
  | arith p => exact lowerArith_allDirect ρ p
  | mem m =>
      rw [lowerMixed, allDirect, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
      exact lowerMem_isDirect m

/-- The whole mixed leaf passes the decidable `allDirect` check. -/
theorem lowerMixedSeq_allDirect (ρ : RegMap) (xs : List MixedOp) :
    allDirect (lowerMixedSeq ρ xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [lowerMixedSeq_cons, allDirect_append, lowerMixed_allDirect, ih,
          Bool.and_self]

/-- **Mixed scalar-ALU + direct-memory leak preservation, `jasminc_preserves_ct`-free.**
    A leaf that interleaves scalar ALU and direct `loadMem`/`storeMem` produces
    the **same** concrete x86 leakage trace from any two states. This strictly
    extends the scalar-only `lowerSeq_constant_time` leg to direct memory
    operations, still entirely on the owned concrete `blockLeak` model. -/
theorem lowerMixedSeq_constant_time (ρ : RegMap) (xs : List MixedOp)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerMixedSeq ρ xs) = blockLeak s₂ (lowerMixedSeq ρ xs) :=
  allDirect_constant_time (lowerMixedSeq ρ xs) (lowerMixedSeq_allDirect ρ xs) s₁ s₂

/-- The mixed leaf has no control-flow (branch) leak. -/
theorem lowerMixedSeq_no_branch (ρ : RegMap) (xs : List MixedOp) (s : JState 64) :
    (blockLeak s (lowerMixedSeq ρ xs)).filter MLeak.isBranch = [] :=
  allDirect_no_branch (lowerMixedSeq ρ xs) s

/-! ## §4. The extended dialect → jasmin → x86 chain

We mirror `DialectLeakRefinement.dialect_jasmin_x86_chain`, with the realization
predicate pointing at the direct-memory (resp. mixed) leaf instead of the
scalar-only `lowerSeq`. The dialect → jasmin leg (`leakTraceJ_length_refines`) is
reused verbatim; the jasmin → x86 leg is the direct-memory keystone proved above,
so the whole chain stays `jasminc_preserves_ct`-free. -/

/-- **Realization onto the direct-memory x86 leg.** A dialect program `cc` is
    realized by the direct-memory block `ms` when the concrete x86 code it is
    emitted to is `lowerMemSeq ms` — the direct-addressed, branch-free leaf the
    keystone covers. -/
def RealizesMem {Γ : Ctx} {t : CryptoTy}
    (_cc : Com catCryptDialect Γ t)
    (ms : List MemOp) (tgt : List (JInstr 64)) : Prop :=
  tgt = lowerMemSeq ms

/-- **Realization onto the mixed scalar+direct-memory x86 leg.** -/
def RealizesMixed {Γ : Ctx} {t : CryptoTy}
    (_cc : Com catCryptDialect Γ t)
    (ρ : RegMap) (xs : List MixedOp) (tgt : List (JInstr 64)) : Prop :=
  tgt = lowerMixedSeq ρ xs

/-- **The dialect → jasmin → x86 chain, direct-memory fragment.** For a dialect
    program `cc` that lowers through the front to `jcom`
    (`cryptoDialectToJasminCom cc = some jcom`) and is realized by a direct-memory
    block `ms`:

    * (dialect → jasmin) the leak-length refinement holds
      (`leakTraceJ_length_refines`, reused);
    * (jasmin → x86) the concrete x86 `blockLeak (lowerMemSeq ms)` is
      state-independent and branch-free (`lowerMemSeq_constant_time`,
      `lowerMemSeq_no_branch`).

    Closed on the direct-memory fragment; **no `jasminc_preserves_ct`**. -/
theorem dialect_jasmin_x86_chain_mem {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ) (CryptoToJasminCom.mapTy t))
    (hlow : DialectToJasminCom.cryptoDialectToJasminCom cc = some jcom)
    (ms : List MemOp) (tgt : List (JInstr 64))
    (hreal : RealizesMem cc ms tgt) :
    (leakTraceJ jcom).length = (Com.leakTrace cc).length ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  refine ⟨leakTraceJ_length_refines cc jcom hlow, ?_, ?_⟩
  · subst hreal; intro s₁ s₂; exact lowerMemSeq_constant_time ms s₁ s₂
  · subst hreal; intro s; exact lowerMemSeq_no_branch ms s

/-- **The dialect → jasmin → x86 chain, mixed scalar+direct-memory fragment.**
    The same three legs for a dialect program realized by a mixed scalar-ALU +
    direct-memory leaf `xs`. This is the strict extension of
    `DialectLeakRefinement.dialect_jasmin_x86_chain` (scalar-only) to direct
    `stackLoad`/`stackStore`. **No `jasminc_preserves_ct`**. -/
theorem dialect_jasmin_x86_chain_mixed {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ) (CryptoToJasminCom.mapTy t))
    (hlow : DialectToJasminCom.cryptoDialectToJasminCom cc = some jcom)
    (ρ : RegMap) (xs : List MixedOp) (tgt : List (JInstr 64))
    (hreal : RealizesMixed cc ρ xs tgt) :
    (leakTraceJ jcom).length = (Com.leakTrace cc).length ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  refine ⟨leakTraceJ_length_refines cc jcom hlow, ?_, ?_⟩
  · subst hreal; intro s₁ s₂; exact lowerMixedSeq_constant_time ρ xs s₁ s₂
  · subst hreal; intro s; exact lowerMixedSeq_no_branch ρ xs s

/-! ## §5. Sharp honesty: the register-indexed memory op is provably NOT CT

The register-indexed (secret-index) ops `loadMemIdx`/`storeMemIdx` are excluded
from the direct-memory fragment **by design**, not because their CT proof is
missing. A secret-indexed access *is* a leak: its effective address is
`scale · (value in the index register)`, so two states differing on the index
register produce different address traces. We re-expose the witness, and
contrast it with the *public*-indexed case, which **is** CT. -/

/-- **The excluded case is provably NOT constant-time** (not a missing proof). A
    register-indexed scatter `storeMemIdx` leaks the index register's *value* into
    its address trace: there are two states whose `blockLeak` traces differ. This
    is `MachineConstantTime.nonCT_storeMemIdx_leaks_value`, re-exposed here to make
    the boundary explicit: the register-indexed memory op is *inherently*
    value-dependent, so it is correctly outside the direct-memory fragment — the
    "remaining" register-indexed case is not a gap to close but an honest
    non-CT property. -/
theorem regIndexed_provably_not_CT :
    ∃ s₁ s₂ : JState 64,
      blockLeak s₁ indexedScatterLeaf ≠ blockLeak s₂ indexedScatterLeaf :=
  nonCT_storeMemIdx_leaks_value

/-- **The honest dual: a *public*-indexed access IS constant-time.** The exclusion
    in §5 is about *secret* indices, not indexed addressing in general. A memory
    op indexed by a *public* loop counter (a Merkle/FRI position) is constant-time
    in the standard sense: any two states agreeing on the public registers produce
    the same trace. This is `MachineConstantTime.pubIndexedLeaf_constant_time`,
    re-exposed to fix the precise boundary — secret-vs-public index, not
    direct-vs-indexed. -/
theorem pubIndexed_is_CT (s₁ s₂ : JState 64)
    (hag : agreePub demoPub s₁ s₂) :
    blockLeak s₁ pubIndexedLeaf = blockLeak s₂ pubIndexedLeaf :=
  pubIndexedLeaf_constant_time s₁ s₂ hag

end CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinementMem
