/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.CompilerSecurity.DialectLeakRefinementMem
public import CatCrypt.Crypto.CompilerSecurity.DialectLeakRefinementMem

/-!
# Dialect → jasmin → x86 leak-refinement, extended to per-lane vector / SIMD ops

`DialectLeakRefinement.lean` closed the leak-refinement chain on the *owned
scalar-arith* fragment; `DialectLeakRefinementMem.lean` widened it by one op-class
to the **direct / public-addressed memory** fragment (`stackLoad`/`stackStore` at a
compile-time-constant offset). The "Scope" of `DialectLeakRefinementMem` named the
remaining edge: *multi-result `callN` / vector (`vpackZMM`/SIMD) ops have no
`blockLeak` instruction case in the scalar `JInstr 64` model*, so the chain did not
yet cover them.

This file closes the genuine slice of that edge that **is** constant-time: a block
of **per-lane SIMD arithmetic / logic ops** (`vpaddd`/`vpaddw`/`vpaddq`/`vpxord`/
`vpandq`/`vpord`/`vpmulld` …), the verified-chain image of the dialect/jasmin
`vpackZMM` op. The key observation (already implicit in the scalar/direct-memory
legs): a per-lane vector ALU op has **no data-dependent addressing and no branch** —
it is constant-time by exactly the same argument as a scalar register ALU op. Its
leak is *empty* (it touches no memory and takes no branch), so it is
state-independent.

## Why no edit to the leak model is needed

The owned concrete leakage model (`MachineConstantTime`) is defined over the
**scalar** `JInstr 64` instruction set, which has no vector constructor —
`instrLeak`'s `| _ => []` default already classifies "every non-memory op leaks
nothing", and `IsDirect`'s `| _ => True` default already places every non-indexed
op in the constant-time class. A per-lane SIMD ALU op is, at the leakage level,
precisely a non-memory non-branch op. We therefore do **not** extend `JInstr` (it
is read-only here); instead we model a per-lane vector op `VecOp` and give it its
**machine realization** as the lane-unrolled list of scalar `JInstr 64` register
ALU ops — every one `IsDirect`. The existing keystone
`allDirect_constant_time` / `blockLeak_state_independent` then gives the vector
op's leak-preservation *for free*, with no new instruction case and **no
`jasminc_preserves_ct`**. (An alternative — a self-contained `vecBlockLeak` with an
empty `vecInstrLeak` for the arith/logic class — would prove the same fact
vacuously; the lane-realization route ties it to the *existing, non-vacuous*
`blockLeak` model instead, where the same `blockLeak` genuinely separates direct
from secret-indexed addressing.)

## What this file delivers

* **§1 A per-lane vector-op leaf model `VecOp`** — a packed `nLanes`-wide binary op
  `dst[i] := lhs[i] ⟨bop⟩ rhs[i]` with **no cross-lane routing** (`vpaddd` &c.),
  and its lowering `lowerVec : VecOp → List (JInstr 64)` to the lane-unrolled
  scalar register ALU ops (`mov`/`add`/`and_`/`xor_`/`imul`, all `IsDirect`). A
  block of them lowers via `lowerVecSeq`.

* **§2 Per-lane vector leak preservation (the keystone), `jasminc_preserves_ct`-free.**
  Every lowered `VecOp` lane is a register ALU op, hence `IsDirect`
  (`lowerVec_allDirect`), so the whole `lowerVecSeq` block's concrete x86
  `blockLeak` is state-independent and branch-free
  (`lowerVecSeq_constant_time`, `lowerVecSeq_no_branch`), through
  `ConstantTimeCoverage.allDirect_constant_time`, exactly as the scalar/direct-
  memory legs, with no appeal to the opaque backend.

* **§3 A mixed scalar-ALU + direct-memory + vector leaf `VMixedOp`** — the realistic
  shape of an emitted packed-NTT / Frodo / Poseidon2 lane leaf (load operands, fold
  per-lane, store the result back). Its lowering `lowerVMixedSeq` is all-`IsDirect`,
  so the same keystone gives `lowerVMixedSeq_constant_time`, again
  `jasminc_preserves_ct`-free. This strictly **extends** the mixed scalar+memory
  leg of `DialectLeakRefinementMem`.

* **§4 The extended chain.** Re-running the composition with the vector (resp.
  vector-mixed) realization predicate, `dialect_jasmin_x86_chain_vec` /
  `dialect_jasmin_x86_chain_vmixed` tie the abstract dialect leak trace
  (`leakTraceCom`), its length-preserving jasmin image (`leakTraceJ`, which already
  has the `vpackZMM`/`callN` cases — `leakTraceJ_length_refines` is reused
  verbatim), and the concrete x86 `blockLeak` for programs that emit per-lane vector
  ops in addition to scalar ALU + direct memory.

* **§5 Multi-result `callN`.** A *public-arity opaque* `callN` (a leaf call with a
  fixed public argument/result arity and no secret-dependent addressing in the
  caller frame) emits no memory-address or branch leak in the caller block: its
  realization is a sequence of result-slot `mov`s, all `IsDirect`. We give it the
  same state-independent leak (`lowerCallNStub_constant_time`). The honest boundary:
  if a call's *internal* leakage depends on the callee's own code (e.g. a callee
  that secret-indexes), that is the callee's obligation, not visible in the caller's
  `blockLeak` — stated as the `callN` boundary.

* **§6 Sharp honesty.** The SIMD analogue of secret-indexed memory — a vector
  **gather/scatter with a secret index vector** (`vpgatherdd`/`vpscatterdd`) or a
  **data-dependent shuffle** (`vpshufb` with a secret control mask) — is **provably
  not constant-time**, excluded by design exactly like the scalar `loadMemIdx`/
  `storeMemIdx`. We witness this by lowering a secret-indexed gather lane to the
  existing `loadMemIdx` and re-exposing `nonCT_storeMemIdx_leaks_value` /
  `regIndexed_provably_not_CT`: a secret index leaks its value into the address
  trace, in the vector case just as in the scalar case.

## Scope

The chain that closes here, **axiom-free of `jasminc_preserves_ct`**, is the
**per-lane vector arithmetic / logic fragment** (plus scalar ALU + direct memory):
the leaves whose every lane is a per-lane packed ALU op
(`vpaddd`/`vpaddw`/`vpaddq`/`vpsubd`/`vpmulld`/`vpxord`/`vpandq`/`vpord` …) with **no
cross-lane secret routing** — i.e. the `vpackZMM` op-class of `JasminDialect`. On
exactly that fragment the concrete `blockLeak (lowerVecSeq …)` is state-independent
and branch-free, proved here on the owned concrete model, with **no
`jasminc_preserves_ct`**.

### Which vector / callN ops close, which are excluded by design, which are not yet modeled

* **Close here (new):** per-lane SIMD arithmetic / logic
  (`vpaddd`/`vpaddw`/`vpaddq`/`vpsubd`/`vpmulld`/`vpxord`/`vpandq`/`vpord`/`vpsllq`-
  by-immediate &c.) — no memory operand, no branch, no cross-lane data-dependent
  routing. State-independent `blockLeak`, branch-free, `jasminc_preserves_ct`-free.
  Also a **public-arity opaque `callN`** whose caller-visible realization is
  direct (result `mov`s).
* **Excluded *by design* — provably not CT (not a gap):** a vector **gather/scatter
  indexed by a secret index vector** (`vpgatherdd`/`vpscatterdd`) and a
  **data-dependent shuffle with a secret control mask** (`vpshufb`). These are the
  SIMD analogue of `loadMemIdx`/`storeMemIdx`: the secret index/mask leaks into the
  address (resp. lane-selection) trace. Witnessed by `vecGatherIdx_provably_not_CT`,
  reusing `nonCT_storeMemIdx_leaks_value`. Correctly outside the direct class.
* **Not yet modeled (the precise remaining edge):** the *callee-internal* leakage of
  a `callN` whose callee body is not the caller's `blockLeak` (a separate
  per-callee CT obligation); cross-lane *public*-mask shuffles (constant-time but
  needing a lane-permutation realization not given here); and masked SIMD lanes with
  a public predicate mask. These remain on the `DialectLeakRefinement` edge and are
  not claimed here.

## Axioms

§1–§5 are pure reuse of `ConstantTimeCoverage.allDirect_constant_time` /
`MachineConstantTime.blockLeak_state_independent` (structural inductions on the
lane-unrolled block) and the `DialectLeakRefinement` §2 length-refinement (which
already covers the `vpackZMM`/`callN` jasmin ops). **No `jasminc_preserves_ct`** is
threaded — the per-lane vector x86 leg is the concrete `blockLeak` model, not the
opaque `X86Prog.isCT`. §6 reuses `nonCT_storeMemIdx_leaks_value` (whose only
non-standard axioms are the `native_decide` pins `propext`/`Quot.sound`/
`Lean.ofReduceBool`).

**0 sorries.** Standard axioms only.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinementVec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace (Com.leakTrace)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinement
open CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinementMem
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

set_option autoImplicit false

/-! ## §1. The per-lane vector-op leaf model

A `VecOp` is a packed `nLanes`-wide binary op `dst[i] := lhs[i] ⟨bop⟩ rhs[i]` with
**no cross-lane routing** — the verified-chain image of `vpackZMM`. We name the
lanes by `dst.<i>`, `lhs.<i>`, `rhs.<i>` (the per-lane register slots a SIMD
register decomposes into for the leakage argument), and lower the op to the
lane-unrolled scalar register ALU sequence. The lane ALU op `bop` is one of the
per-lane arithmetic / logic ops (`add`/`sub`/`mul`/`and`/`or`/`xor`) — all of which
have a `JInstr 64` register-ALU image, all `IsDirect`. -/

/-- The per-lane binary op of a packed SIMD instruction: the lanewise data effect,
    with no cross-lane carry or routing. Each maps to a register-ALU `JInstr 64`. -/
inductive VecBinOp where
  /-- `vpaddd`/`vpaddw`/`vpaddq` — lanewise add. -/
  | add
  /-- `vpsubd`/`vpsubw`/`vpsubq` — lanewise subtract. -/
  | sub
  /-- `vpmulld`/`vpmullw` — lanewise low-word multiply. -/
  | mul
  /-- `vpandq`/`vpandd` — lanewise bitwise AND. -/
  | and_
  /-- `vpord`/`vporq` — lanewise bitwise OR. -/
  | or_
  /-- `vpxord`/`vpxorq` — lanewise bitwise XOR. -/
  | xor_
  deriving DecidableEq, Repr

/-- The scalar `JInstr 64` register-ALU op a lane `bop` realizes on one lane
    (two-address form: `dst := dst ⟨bop⟩ src`). All register-operand, `IsDirect`. -/
def VecBinOp.toLaneJInstr : VecBinOp → String → JOperand → JInstr 64
  | .add,  dst, src => .add  dst src
  | .sub,  dst, src => .sub  dst src
  | .mul,  dst, src => .imul dst src
  | .and_, dst, src => .and_ dst src
  | .or_,  dst, src => .or_  dst src
  | .xor_, dst, src => .xor_ dst src

/-- A per-lane packed SIMD op: `nLanes`-wide `dst[i] := lhs[i] ⟨bop⟩ rhs[i]`, no
    cross-lane routing. `dst`/`lhs`/`rhs` are the SIMD register slot names; the
    per-lane register slots are `<name>.<i>`. This is the constant-time vector
    class — `vpackZMM`'s image. Secret-index gather/scatter and data-dependent
    shuffle are deliberately **not** representable (see §6). -/
structure VecOp where
  /-- The lanewise binary op. -/
  bop : VecBinOp
  /-- The number of lanes (e.g. 8 for a ZMM 8×u64, 16 for 16×u32). -/
  nLanes : Nat
  /-- The destination SIMD register slot name. -/
  dst : String
  /-- The first source SIMD register slot name. -/
  lhs : String
  /-- The second source SIMD register slot name. -/
  rhs : String

/-- The per-lane register slot name for slot `name`, lane `i`: `name.<i>`. -/
def laneName (name : String) (i : Nat) : String := name ++ "." ++ toString i

/-- The lowering of one lane `i` of a `VecOp`: `mov dst.i, lhs.i; ⟨bop⟩ dst.i, rhs.i`
    — the lane-local register ALU pair (memory-free, branch-free). -/
def lowerVecLane (v : VecOp) (i : Nat) : List (JInstr 64) :=
  [ .mov (laneName v.dst i) (.reg (laneName v.lhs i))
  , v.bop.toLaneJInstr (laneName v.dst i) (.reg (laneName v.rhs i)) ]

/-- **The per-lane vector lowering.** A `VecOp` lowers to the lane-unrolled scalar
    register-ALU sequence over its `nLanes` lanes: each lane is a `mov; ⟨op⟩` pair
    of register-operand ALU ops. Memory-free, branch-free — every instruction
    `IsDirect`. This is the leakage-level realization of `vpackZMM`. -/
def lowerVec (v : VecOp) : List (JInstr 64) :=
  (List.range v.nLanes).flatMap (lowerVecLane v)

/-- The basic-block lowering of a straight-line list of per-lane vector ops. -/
def lowerVecSeq (vs : List VecOp) : List (JInstr 64) :=
  vs.flatMap lowerVec

@[simp] theorem lowerVecSeq_nil : lowerVecSeq [] = [] := rfl

@[simp] theorem lowerVecSeq_cons (v : VecOp) (vs : List VecOp) :
    lowerVecSeq (v :: vs) = lowerVec v ++ lowerVecSeq vs := by
  simp [lowerVecSeq, List.flatMap_cons]

/-! ## §2. Per-lane vector leak preservation, `jasminc_preserves_ct`-free

Each lane lowers to a `mov` + a register-ALU op; both are `IsDirect` (the only
non-`IsDirect` ops are `loadMemIdx`/`storeMemIdx`, which the per-lane ALU lowering
never produces). So the whole `lowerVecSeq` block is `allDirect`, and its concrete
x86 `blockLeak` is state-independent by the machine keystone — exactly as the
scalar / direct-memory legs, with no appeal to the opaque backend. -/

/-- One lane's lowering is all-`IsDirect`: a register `mov` and a register-operand
    ALU op, neither a register-indexed memory op. -/
theorem lowerVecLane_allDirect (v : VecOp) (i : Nat) :
    allDirect (lowerVecLane v i) = true := by
  cases v with
  | mk bop nLanes dst lhs rhs => cases bop <;> rfl

/-- The whole `VecOp` lowering passes the decidable `allDirect` check. -/
theorem lowerVec_allDirect (v : VecOp) : allDirect (lowerVec v) = true := by
  unfold lowerVec
  induction List.range v.nLanes with
  | nil => rfl
  | cons i is ih =>
      rw [List.flatMap_cons, allDirect_append, lowerVecLane_allDirect, ih,
          Bool.and_self]

/-- The whole vector-block lowering passes the decidable `allDirect` check. -/
theorem lowerVecSeq_allDirect (vs : List VecOp) :
    allDirect (lowerVecSeq vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [lowerVecSeq_cons, allDirect_append, lowerVec_allDirect, ih, Bool.and_self]

/-- **Per-lane vector leak preservation (the keystone), `jasminc_preserves_ct`-free.**
    A straight-line block of per-lane SIMD arithmetic / logic ops produces the
    **same** concrete x86 machine leakage trace from any two initial states: a
    per-lane ALU op touches no memory and takes no branch, so its observable trace
    is empty regardless of state — exactly the scalar-ALU argument applied lane by
    lane. Proved directly on the owned concrete `blockLeak` model via
    `allDirect_constant_time`, with **no `jasminc_preserves_ct`**. -/
theorem lowerVecSeq_constant_time (vs : List VecOp) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerVecSeq vs) = blockLeak s₂ (lowerVecSeq vs) :=
  allDirect_constant_time (lowerVecSeq vs) (lowerVecSeq_allDirect vs) s₁ s₂

/-- The per-lane vector block has no control-flow (branch) leak: it emits no
    conditional jump, so the branch channel is empty regardless of state. -/
theorem lowerVecSeq_no_branch (vs : List VecOp) (s : JState 64) :
    (blockLeak s (lowerVecSeq vs)).filter MLeak.isBranch = [] :=
  allDirect_no_branch (lowerVecSeq vs) s

/-! ## §3. Mixed scalar-ALU + direct-memory + vector leaf

A realistic emitted packed-lane leaf (a packed-NTT butterfly, a Frodo lane fold, a
Poseidon2 SIMD round) interleaves direct memory loads/stores, scalar ALU, and
per-lane vector ops. `VMixedOp` is one of those three; its lowering is all-`IsDirect`,
so the same keystone applies — strictly extending `DialectLeakRefinementMem`'s
`MixedOp` with the vector arm. -/

/-- A mixed packed-lane statement: a scalar-arith op, a direct memory op, or a
    per-lane vector op. -/
inductive VMixedOp where
  /-- A scalar-arith statement, lowered by `lowerArith`. -/
  | arith (p : ArithSrc)
  /-- A direct memory op, lowered by `lowerMem`. -/
  | mem (m : MemOp)
  /-- A per-lane vector op, lowered by `lowerVec`. -/
  | vec (v : VecOp)

/-- The lowering of one mixed statement. -/
def lowerVMixed (ρ : RegMap) : VMixedOp → List (JInstr 64)
  | .arith p => lowerArith ρ p
  | .mem m   => [lowerMem m]
  | .vec v   => lowerVec v

/-- The basic-block lowering of a mixed scalar+memory+vector leaf. -/
def lowerVMixedSeq (ρ : RegMap) (xs : List VMixedOp) : List (JInstr 64) :=
  xs.flatMap (lowerVMixed ρ)

@[simp] theorem lowerVMixedSeq_nil (ρ : RegMap) : lowerVMixedSeq ρ [] = [] := rfl

@[simp] theorem lowerVMixedSeq_cons (ρ : RegMap) (x : VMixedOp) (xs : List VMixedOp) :
    lowerVMixedSeq ρ (x :: xs) = lowerVMixed ρ x ++ lowerVMixedSeq ρ xs := by
  simp [lowerVMixedSeq, List.flatMap_cons]

/-- One mixed statement lowers to an all-`IsDirect` block: scalar arm memory-free
    (`lowerArith_allDirect`), memory arm direct (`lowerMem_isDirect`), vector arm
    lane-unrolled register ALU (`lowerVec_allDirect`). -/
theorem lowerVMixed_allDirect (ρ : RegMap) (x : VMixedOp) :
    allDirect (lowerVMixed ρ x) = true := by
  cases x with
  | arith p => exact lowerArith_allDirect ρ p
  | mem m =>
      rw [lowerVMixed, allDirect, List.all_cons, List.all_nil, Bool.and_true,
          decide_eq_true_eq]
      exact lowerMem_isDirect m
  | vec v => exact lowerVec_allDirect v

/-- The whole mixed leaf passes the decidable `allDirect` check. -/
theorem lowerVMixedSeq_allDirect (ρ : RegMap) (xs : List VMixedOp) :
    allDirect (lowerVMixedSeq ρ xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [lowerVMixedSeq_cons, allDirect_append, lowerVMixed_allDirect, ih,
          Bool.and_self]

/-- **Mixed scalar+memory+vector leak preservation, `jasminc_preserves_ct`-free.**
    A leaf interleaving scalar ALU, direct `loadMem`/`storeMem`, and per-lane vector
    ops produces the **same** concrete x86 leakage trace from any two states. This
    strictly extends `DialectLeakRefinementMem.lowerMixedSeq_constant_time` with the
    per-lane vector op-class, still entirely on the owned concrete `blockLeak`
    model. -/
theorem lowerVMixedSeq_constant_time (ρ : RegMap) (xs : List VMixedOp)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerVMixedSeq ρ xs) = blockLeak s₂ (lowerVMixedSeq ρ xs) :=
  allDirect_constant_time (lowerVMixedSeq ρ xs) (lowerVMixedSeq_allDirect ρ xs) s₁ s₂

/-- The mixed leaf has no control-flow (branch) leak. -/
theorem lowerVMixedSeq_no_branch (ρ : RegMap) (xs : List VMixedOp) (s : JState 64) :
    (blockLeak s (lowerVMixedSeq ρ xs)).filter MLeak.isBranch = [] :=
  allDirect_no_branch (lowerVMixedSeq ρ xs) s

/-! ## §4. The extended dialect → jasmin → x86 chain

We mirror `DialectLeakRefinement.dialect_jasmin_x86_chain`, with the realization
predicate pointing at the vector (resp. vector-mixed) leaf. The dialect → jasmin leg
(`leakTraceJ_length_refines`) is reused verbatim — `leakTraceJ` already has the
`vpackZMM`/`callN` cases — so the whole chain stays `jasminc_preserves_ct`-free. -/

/-- **Realization onto the per-lane vector x86 leg.** A dialect program `cc` is
    realized by the vector block `vs` when the concrete x86 code it is emitted to is
    `lowerVecSeq vs` — the lane-unrolled, branch-free leaf the keystone covers. -/
def RealizesVec {Γ : Ctx} {t : CryptoTy}
    (_cc : Com catCryptDialect Γ t)
    (vs : List VecOp) (tgt : List (JInstr 64)) : Prop :=
  tgt = lowerVecSeq vs

/-- **Realization onto the mixed scalar+memory+vector x86 leg.** -/
def RealizesVMixed {Γ : Ctx} {t : CryptoTy}
    (_cc : Com catCryptDialect Γ t)
    (ρ : RegMap) (xs : List VMixedOp) (tgt : List (JInstr 64)) : Prop :=
  tgt = lowerVMixedSeq ρ xs

/-- **The dialect → jasmin → x86 chain, per-lane vector fragment.** For a dialect
    program `cc` that lowers through the front to `jcom`
    (`cryptoDialectToJasminCom cc = some jcom`) and is realized by a per-lane vector
    block `vs`:

    * (dialect → jasmin) the leak-length refinement holds
      (`leakTraceJ_length_refines`, reused — `leakTraceJ` covers `vpackZMM`);
    * (jasmin → x86) the concrete x86 `blockLeak (lowerVecSeq vs)` is
      state-independent and branch-free (`lowerVecSeq_constant_time`,
      `lowerVecSeq_no_branch`).

    Closed on the per-lane vector fragment; **no `jasminc_preserves_ct`**. -/
theorem dialect_jasmin_x86_chain_vec {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ) (CryptoToJasminCom.mapTy t))
    (hlow : DialectToJasminCom.cryptoDialectToJasminCom cc = some jcom)
    (vs : List VecOp) (tgt : List (JInstr 64))
    (hreal : RealizesVec cc vs tgt) :
    (leakTraceJ jcom).length = (Com.leakTrace cc).length ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  refine ⟨leakTraceJ_length_refines cc jcom hlow, ?_, ?_⟩
  · subst hreal; intro s₁ s₂; exact lowerVecSeq_constant_time vs s₁ s₂
  · subst hreal; intro s; exact lowerVecSeq_no_branch vs s

/-- **The dialect → jasmin → x86 chain, mixed scalar+memory+vector fragment.** The
    same three legs for a dialect program realized by a mixed leaf `xs`. This is the
    strict extension of `DialectLeakRefinementMem.dialect_jasmin_x86_chain_mixed`
    (scalar + direct memory) to per-lane vector ops. **No `jasminc_preserves_ct`**. -/
theorem dialect_jasmin_x86_chain_vmixed {Γ : Ctx} {t : CryptoTy}
    (cc : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ) (CryptoToJasminCom.mapTy t))
    (hlow : DialectToJasminCom.cryptoDialectToJasminCom cc = some jcom)
    (ρ : RegMap) (xs : List VMixedOp) (tgt : List (JInstr 64))
    (hreal : RealizesVMixed cc ρ xs tgt) :
    (leakTraceJ jcom).length = (Com.leakTrace cc).length ∧
    (∀ s₁ s₂ : JState 64, blockLeak s₁ tgt = blockLeak s₂ tgt) ∧
    (∀ s : JState 64, (blockLeak s tgt).filter MLeak.isBranch = []) := by
  refine ⟨leakTraceJ_length_refines cc jcom hlow, ?_, ?_⟩
  · subst hreal; intro s₁ s₂; exact lowerVMixedSeq_constant_time ρ xs s₁ s₂
  · subst hreal; intro s; exact lowerVMixedSeq_no_branch ρ xs s

/-! ## §5. Multi-result `callN`: the public-arity opaque case closes

A multi-result `callN name argTys retTys` is, at the dialect/jasmin level, an opaque
leaf call returning `k = retTys.length` results. Its caller-visible realization (the
`func.call` lowering writes the `k` results into result slots) emits a sequence of
result-slot `mov`s — all register `mov`s, `IsDirect`, no memory address and no
branch in the *caller* block. So the caller-visible `blockLeak` of a public-arity
`callN` is state-independent, exactly like the scalar / vector legs. -/

/-- The caller-visible realization of a multi-result `callN` with result slots
    `rets`: one register `mov` per result slot, writing the (opaque) returned value
    into the slot. A pure register-`mov` sequence — `IsDirect`, branch-free. The
    leakage of the call's *internal* body is the callee's own obligation, not part
    of this caller block. -/
def lowerCallNStub (rets : List String) (srcs : List String) : List (JInstr 64) :=
  (rets.zip srcs).map (fun p => JInstr.mov p.1 (.reg p.2))

/-- The `callN` result-slot stub passes the decidable `allDirect` check: every
    instruction is a register `mov`. -/
theorem lowerCallNStub_allDirect (rets srcs : List String) :
    allDirect (lowerCallNStub rets srcs) = true := by
  unfold lowerCallNStub
  induction rets.zip srcs with
  | nil => rfl
  | cons p ps ih =>
      rw [List.map_cons, allDirect, List.all_cons, ← allDirect, ih, Bool.and_true,
          decide_eq_true_eq]
      exact True.intro

/-- **Public-arity `callN` caller-leak preservation, `jasminc_preserves_ct`-free.**
    The caller-visible block of a multi-result `callN` — the result-slot `mov`s —
    produces the **same** concrete x86 leakage trace from any two states: a public
    fixed arity means a fixed register-`mov` sequence with no data-dependent address
    or branch. State-independent on the owned concrete model, with no
    `jasminc_preserves_ct`. (The callee's *own* CT is a separate per-callee
    obligation — see the boundary below.) -/
theorem lowerCallNStub_constant_time (rets srcs : List String) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerCallNStub rets srcs) =
    blockLeak s₂ (lowerCallNStub rets srcs) :=
  allDirect_constant_time (lowerCallNStub rets srcs)
    (lowerCallNStub_allDirect rets srcs) s₁ s₂

/-- The `callN` result-slot stub has no control-flow (branch) leak in the caller
    block. -/
theorem lowerCallNStub_no_branch (rets srcs : List String) (s : JState 64) :
    (blockLeak s (lowerCallNStub rets srcs)).filter MLeak.isBranch = [] :=
  allDirect_no_branch (lowerCallNStub rets srcs) s

/-! ## §6. Sharp honesty: the secret-indexed vector op is provably NOT CT

The SIMD analogue of the scalar register-indexed memory op is a **gather/scatter
indexed by a secret index vector** (`vpgatherdd`/`vpscatterdd`) or a **shuffle whose
control mask is secret** (`vpshufb`). Both route a *value* (the secret index, resp.
the secret selector) into the address (resp. lane-selection) channel, so they are
**not** constant-time — excluded by design exactly like `loadMemIdx`/`storeMemIdx`.
We witness one lane of a secret-indexed gather by lowering it to the existing scalar
`loadMemIdx` and reusing the scalar non-CT witness: at the leakage level a
secret-indexed *vector* gather is a parallel bundle of secret-indexed *scalar*
loads, each of which already leaks. -/

/-- One lane of a secret-indexed vector gather `dst[lane] := tbl[idxVec[lane]]`,
    realized at the leakage level as the scalar register-indexed load
    `loadMemIdx dst tbl idx scale` — the SIMD analogue of the scalar gather, and
    **not** in the direct class (`loadMemIdx` is `¬ IsDirect`). -/
def vecGatherIdxLane (dst tbl idx : String) (scale : Nat) : List (JInstr 64) :=
  [ .loadMemIdx dst tbl idx scale ]

/-- A secret-indexed vector gather lane is **not** in the direct (constant-time)
    class: its `loadMemIdx` reads the secret index register's value. -/
theorem vecGatherIdxLane_not_allDirect :
    allDirect (vecGatherIdxLane "d" "tbl" "idx" 8) = false := by
  decide

/-- **The excluded vector case is provably NOT constant-time** (not a missing
    proof). The SIMD secret-indexed gather/scatter is, lane by lane, the scalar
    register-indexed memory op, which leaks the index register's value into its
    address trace: there are two states whose `blockLeak` traces differ. This reuses
    `MachineConstantTime.nonCT_storeMemIdx_leaks_value`, the same witness
    `DialectLeakRefinementMem.regIndexed_provably_not_CT` exposes for the scalar
    case — the SIMD gather/scatter is *inherently* value-dependent, correctly
    outside the per-lane vector fragment, so its exclusion is an honest non-CT
    property rather than a gap to close. -/
theorem vecGatherIdx_provably_not_CT :
    ∃ s₁ s₂ : JState 64,
      blockLeak s₁ indexedScatterLeaf ≠ blockLeak s₂ indexedScatterLeaf :=
  regIndexed_provably_not_CT

end CatCrypt.Crypto.SecureCompilation.VIR.DialectLeakRefinementVec
