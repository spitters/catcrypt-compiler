/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose
import CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT

/-!
# The owned-pipeline robustness capstone: security **and** constant-time, unified

This module answers the external audit's **parity point (c)**: that
cryptographic-security preservation and constant-time (CT) preservation should
be carried *together*, down the *same* compiler, as **one** guarantee — neither
alone being "the full Jasmin result". For the **owned** `LowCT → JInstr`
pipeline (the straight-line scalar-arith fragment our backend emits itself) we
prove exactly this: a single theorem, over one lowering of one source program,
that returns the conjunction of

1. **cryptographic-security preservation** — an `sdist ≤ ε` bound to an ideal
   transfers from the source program to the compiled kernel
   (`LowCTSecPreserve.compiled_preserves_security`, whole-function variant
   `LowCTCallCompose.wholeFn_preserves_security`); **and**
2. **constant-time** — the compiled `JInstr` block's machine leakage trace
   (`blockLeak`, and its unified-alphabet lift `blockLeakU`) is
   state-independent, and stays so under register rename + spill
   (`RegAllocSpillCT.ourLowering_spill_constant_time`) and under linking with
   any direct-addressed context (`LowCTRobustCT.robust_CT`),

for the **same** compiled artifact, down the **same** `LowCT → JInstr` chain.

## Axiom-freeness of `jasminc_preserves_ct` — the contribution

The framework's full-pipeline RHP theorem
(`LowCTRHPFull.RHP_pipeline_full_labeled`) delivers machine-level CT for the
*general* (un-owned) Jasmin backend only by bridging the abstract predicate
`X86Prog.isCT` through the cited axiom `jasminc_preserves_ct` (Arranz-Olmos et
al., arXiv 2511.11292). That axiom is the right move for a backend we do **not**
own.

For the leaves our pipeline emits itself, the leakage model (`blockLeak`) is
concrete and the CT keystones are fully *proved* — not axiom-bridged. So this
capstone carries **both** guarantees with **no** `jasminc_preserves_ct` in its
trust set (verify: `#print axioms ownedCompile_secure_and_CT` shows only
`propext`, `Classical.choice`, `Quot.sound`). The owned-model CT is therefore
the route to *discharge* `jasminc_preserves_ct` in `RHP_pipeline_full_labeled`
for owned leaves, rather than assume it.

## On back-translation (audit point 2), stated honestly

Robust-preservation proofs in general construct a non-identity *back-translation*
of an adversarial target context into a source context. We do not need a
non-trivial one here, and the honest reason is the *strength* of our correctness
result, not a shortcut:

* **Functional / value observation.** Our compiler preserves the **full
  observational denotation**: `progEquiv` is `SPComp`-denotation *equality*
  derived from `compile_correct` (`LowCTSecPreserve.interpSP_progEquiv`,
  `LowCTCallCompose.wholeFn_progEquiv`). Source and target are observationally
  *equal*, not merely refinement-related. This is the full-abstraction case, in
  which the correct back-translation for the functional observation **is the
  identity** — there is nothing to construct.

* **Leakage / timing observation.** The extra observation an adversarial context
  could exploit beyond the functional value is the *leakage* (control-flow +
  memory-address timing). The CT conjunct shows that observation is
  secret-independent (`blockLeak`/`blockLeakU` state-independence), and stable
  under linking (`robust_CT`). So the adversary gains nothing from it either.

Hence, for the owned fragment, **robust security = full-observational
equivalence (functional) + constant-time (leakage)**. The genuinely non-identity
back-translation is the technique needed for compilers that are only
*refinements* (not equivalences); ours is an equivalence **plus** CT, so the
identity back-translation is correct here.

## Honest residuals (audit point (b))

This is the unification for the **bounded owned fragment** (straight-line
scalar-arith leaves, the whole-function variant threading identical call
structure). Two residuals remain, exactly as the audit notes:

* the general **non-equivalence** back-translation — for stages where the
  compiler is a refinement rather than an equivalence — is out of scope here;
* **extending past the owned leaves** to the general un-owned backend still
  routes through `jasminc_preserves_ct` in `RHP_pipeline_full_labeled`. This
  capstone is what would *discharge* that axiom leaf-by-leaf as the owned
  fragment grows; it does not by itself remove the axiom from the general
  pipeline.

## Iris-freeness

The import closure is the owned `X86Backend` security + CT files only
(`LowCTSecPreserve`, `LowCTCallCompose`, `RegAllocSpillCT`, `LowCTRobustCT`).
Nothing under `Bridges/` or `IrisBridge/`: no guarded ITrees, no step-indexing,
no separation logic.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCompileRobust

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTCallCompose
open CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT
open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open scoped ENNReal

/-! ## 1. The bundled guarantee

`SecureAndCT` packages the two preservation facts the audit wants carried
together: for one compiled artifact, the security bound *and* (several layers
of) constant-time. We bundle them as a structure so the capstone returns a
single object whose two fields are the two guarantees, over the same lowering of
the same program. -/

/-- **The unified owned-pipeline guarantee.**  For a compiled scalar-arith
    kernel `tgtP` (lowered by `ρ` to the `JInstr` block `lowerSeq ρ tgtP`), the
    two robustness guarantees the audit wants carried *together*:

    * `security` — the compiled kernel's `SPComp` denotation is within `sdist ≤ ε`
      of the ideal (cryptographic-security preservation);
    * `constant_time` — the compiled `JInstr` block has a state-independent
      machine leakage trace (constant-time).

    Both refer to the **same** `tgtP` / `lowerSeq ρ tgtP`, i.e. one artifact down
    one `LowCT → JInstr` chain. -/
structure SecureAndCT {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) (ε : ℝ≥0∞) : Prop where
  /-- Cryptographic-security preservation: the compiled kernel is `ε`-close
      (in `sdist`) to the ideal. -/
  security :
    sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
          (fun _ : α => ideal) ≤ ε
  /-- Constant-time: the compiled `JInstr` block leaks the same machine trace
      from any two initial machine states. -/
  constant_time :
    ∀ s₁ s₂ : JState 64,
      blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak s₂ (lowerSeq ρ tgtP)

/-! ## 2. The capstone (call-free fragment)

Compose `compiled_preserves_security` (security transfers from source to
compiled, given the `compile_correct` `srcDenote` agreement) with
`lowerSeq_constant_time` (the compiled block is CT, unconditionally — the
fragment is memory-free), over the **same** `tgtP`. -/

/-- **The owned-pipeline robustness capstone (call-free).**

    For a source scalar-arith program `srcP` and its compilation `tgtP` (with the
    `compile_correct` big-step agreement `hcc : srcDenote srcP rs = srcDenote
    tgtP rs`), if the *source* kernel is `ε`-close (in `sdist`) to an `ideal`,
    then the *same* compiled artifact `tgtP` satisfies **both** owned-pipeline
    robustness guarantees at once:

    1. **cryptographic-security preservation** — the compiled kernel's `SPComp`
       denotation is within `sdist ≤ ε` of the ideal (via
       `compiled_preserves_security`); **and**
    2. **constant-time** — the compiled `JInstr` block `lowerSeq ρ tgtP` has a
       state-independent machine leakage trace (via `lowerSeq_constant_time`).

    Both are about the same `tgtP` / `lowerSeq ρ tgtP`, down the same
    `LowCT → JInstr` chain. The CT half is *proved* over the concrete `blockLeak`
    model, so this carries both guarantees with **no** `jasminc_preserves_ct`
    in the trust set.

    `(secure compilation via SCIO RrHP + deterministic-to-pure lift, bundled with
    owned-model constant-time)` -/
theorem ownedCompile_secure_and_CT {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    SecureAndCT (α := α) h ρ tgtP rs ideal ε where
  security := compiled_preserves_security h srcP tgtP rs ideal hcc hsec
  constant_time := fun s₁ s₂ => lowerSeq_constant_time ρ tgtP s₁ s₂

/-! ## 3. The capstone, with the extra owned-CT layers

The same bundled fact, additionally exposing the *robust* (under-linking) and
*spill-survival* CT layers, all about the same `tgtP`. These are the extra
guarantees that make the CT side the genuine owned-model instance of
robust-compilation, not merely a per-block CT check. -/

/-- **The capstone, expanded with the robust + spill CT layers.**

    Returns, for the same compiled `tgtP`:

    * (security) the `sdist ≤ ε` bound on the compiled kernel;
    * (constant_time) per-block CT of `lowerSeq ρ tgtP`;
    * (constant_time_unified) the *unified-alphabet* CT (`blockLeakU`), the form
      that connects to the framework's `UnifiedTrace` RHP statement;
    * (robust_ct) CT *preserved under linking* with any direct-addressed context
      — the genuinely compositional robust-CT content (not an identity
      back-translation);
    * (spill_ct) CT *surviving register rename + spill insertion* — the full
      `lowering + resident-rename + spill` chain stays constant-time.

    Every conjunct is about the same `tgtP` / `lowerSeq ρ tgtP`, down the same
    `LowCT → JInstr` chain, with no `jasminc_preserves_ct`. -/
theorem ownedCompile_secure_and_CT_full {α : Type}
    {E : UCMonad.ITreeNUC.EventSig} {MemTy : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (srcP tgtP : List ArithSrc) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hcc : srcDenote srcP rs = srcDenote tgtP rs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenoteArith srcP rs))
                  (fun _ : α => ideal) ≤ ε) :
    -- (1) cryptographic-security preservation
    (sdist (fun _ : α => interpSP h (itreeDenoteArith tgtP rs))
           (fun _ : α => ideal) ≤ ε) ∧
    -- (2a) per-block constant-time
    (∀ s₁ s₂ : JState 64,
      blockLeak s₁ (lowerSeq ρ tgtP) = blockLeak s₂ (lowerSeq ρ tgtP)) ∧
    -- (2b) constant-time in the framework's unified alphabet
    (∀ s₁ s₂ : JState 64,
      blockLeakU (E := E) (MemTy := MemTy) s₁ (lowerSeq ρ tgtP) =
      blockLeakU (E := E) (MemTy := MemTy) s₂ (lowerSeq ρ tgtP)) ∧
    -- (2c) constant-time preserved under linking with any direct-addressed ctx
    (∀ (ctx : List (JInstr 64)), allDirect ctx = true → ∀ s₁ s₂ : JState 64,
      blockLeak s₁ (lowerSeq ρ tgtP ++ ctx) =
      blockLeak s₂ (lowerSeq ρ tgtP ++ ctx)) ∧
    -- (2d) constant-time surviving register rename + spill insertion
    (∀ (ρspill : String → String) (frameBase : String)
       (slots : String → Option Int) (s₁ s₂ : JState 64),
      blockLeak s₁ (spillRewrite ρspill frameBase slots (lowerSeq ρ tgtP)) =
      blockLeak s₂ (spillRewrite ρspill frameBase slots (lowerSeq ρ tgtP))) :=
  ⟨ compiled_preserves_security h srcP tgtP rs ideal hcc hsec
  , fun s₁ s₂ => lowerSeq_constant_time ρ tgtP s₁ s₂
  , fun s₁ s₂ => lowerSeq_unifiedCT (E := E) (MemTy := MemTy) ρ tgtP s₁ s₂
  , fun ctx hctx s₁ s₂ => lowerSeq_robust_CT ρ tgtP ctx hctx s₁ s₂
  , fun ρspill frameBase slots s₁ s₂ =>
      ourLowering_spill_constant_time ρ ρspill frameBase slots tgtP s₁ s₂ ⟩

/-! ## 4. The whole-function variant (with calls)

Compose the P4.4 capstone `wholeFn_preserves_security` (security threaded through
the call structure) with the same owned-CT layers, for a whole function whose
inter-call scalar segments are lowered to the concatenated `JInstr` block. The
constant-time side is about that compiled scalar block; the security side is
about the whole-function `interpSP` denotation. -/

/-- The compiled `JInstr` block of a whole function's inter-call scalar segments:
    concatenate the per-segment scalar lowerings (`lowerSeq` over each segment's
    `scalars`). The `call`/`vis` nodes are the framework-handled boundary; the
    *machine* CT obligation is on the straight-line scalar code our backend emits
    between calls. -/
def segScalarBlock (ρ : RegMap) (segs : List CallSeg) : List (JInstr 64) :=
  segs.flatMap (fun s => lowerSeq ρ s.scalars)

@[simp] theorem segScalarBlock_nil (ρ : RegMap) : segScalarBlock ρ [] = [] := rfl

@[simp] theorem segScalarBlock_cons (ρ : RegMap) (s : CallSeg) (rest : List CallSeg) :
    segScalarBlock ρ (s :: rest) =
      lowerSeq ρ s.scalars ++ segScalarBlock ρ rest := by
  simp [segScalarBlock, List.flatMap_cons]

/-- The compiled inter-call scalar block of a whole function is `allDirect`:
    every segment's scalar lowering is `allDirect` (`lowerSeq_allDirect`), and
    `allDirect` distributes over concatenation. -/
theorem segScalarBlock_allDirect (ρ : RegMap) (segs : List CallSeg) :
    allDirect (segScalarBlock ρ segs) = true := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    rw [segScalarBlock_cons, allDirect_append, lowerSeq_allDirect, ih, Bool.and_self]

/-- **The whole-function owned-pipeline robustness capstone (with calls).**

    For a source whole function `srcSegs` and its compilation `tgtSegs` (with
    `hag : SegsAgree srcSegs tgtSegs` — identical call structure, per-segment
    `srcDenote` agreement), if the *source* function is `ε`-close to an `ideal`,
    then the *same* compiled function satisfies **both**:

    1. **cryptographic-security preservation** through the call structure (via
       `wholeFn_preserves_security` — each `vis`/call is the same handler
       invocation on both sides, so the call-free argument lifts); **and**
    2. **constant-time** of the compiled inter-call scalar block
       `segScalarBlock ρ tgtSegs` — the straight-line machine code our backend
       emits between calls is state-independent (via `allDirect_constant_time`
       from `segScalarBlock_allDirect`).

    Both refer to the same `tgtSegs`, down the same chain, with no
    `jasminc_preserves_ct`. The call (`vis`) boundary is framework-handled
    identically on both sides; the machine CT obligation lives on the owned
    scalar code, which is what this constant-time conjunct discharges.

    `(secure compilation via SCIO RrHP, lifted through calls, bundled with
    owned-model constant-time)` -/
theorem ownedCompile_wholeFn_secure_and_CT {α : Type}
    (h : ∀ e : callEvents.Event, SPComp (callEvents.Resp e))
    (ρ : RegMap) (srcSegs tgtSegs : List CallSeg) (rs : RustState)
    (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hag : SegsAgree srcSegs tgtSegs)
    (hsec : sdist (fun _ : α => interpSP h (itreeDenote (segToStmts srcSegs) rs))
                  (fun _ : α => ideal) ≤ ε) :
    -- (1) cryptographic-security preservation through the call structure
    (sdist (fun _ : α => interpSP h (itreeDenote (segToStmts tgtSegs) rs))
           (fun _ : α => ideal) ≤ ε) ∧
    -- (2) constant-time of the compiled inter-call scalar block
    (∀ s₁ s₂ : JState 64,
      blockLeak s₁ (segScalarBlock ρ tgtSegs) =
      blockLeak s₂ (segScalarBlock ρ tgtSegs)) :=
  ⟨ wholeFn_preserves_security h srcSegs tgtSegs rs ideal hag hsec
  , fun s₁ s₂ =>
      allDirect_constant_time (segScalarBlock ρ tgtSegs)
        (segScalarBlock_allDirect ρ tgtSegs) s₁ s₂ ⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCompileRobust
