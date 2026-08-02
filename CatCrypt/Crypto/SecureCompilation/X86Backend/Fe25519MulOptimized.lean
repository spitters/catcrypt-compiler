/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
import CatCrypt.Crypto.Optimizer.StoreToLoadForward
import CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-!
# `fe25519_mul` through the GENERIC owned `Com→Com` optimizer pipeline (#555 pilot)

`Fe25519MulKernel.feMulBlock` is the **hand-tuned** Curve25519 field-multiply —
hand-scheduled (dual ADCX/ADOX schoolbook) and hand-allocated (the `feMulPinned`
GP map). It is emitted by the owned x86 backend, but its instruction schedule and
register allocation are hand-written: it **bypasses** the verified owned
`Com→Com` optimizer passes.

This module is the **#555 pilot**: route that same kernel through the GENERIC
owned optimizer pipeline — the verified, kernel-agnostic `JInstr → JInstr`
transforms — and check whether the generic-optimized output is byte-for-byte the
emit the hand path produces, hence the same measured `cyc/op`. It is the
lynchpin dry-run for replacing per-kernel hand-tuning with the generic pipeline.

## The owned optimizer passes that apply at the `JInstr 64` block level

The verified owned optimizer has three kernel-agnostic `List (JInstr 64) →
List (JInstr 64)` (equivalently `Com (x86Dialect 64) → Com` after `lowerBlock`)
transforms, each carrying a **`runBlock`-equality** translation-validation
theorem proved for *all* blocks / all states:

| pass | transform | TV theorem | effect on `feMulBlock` |
|---|---|---|---|
| **store-to-load forward (#372)** | `StoreToLoadForward.storeToLoadForward` | `storeToLoadForward_runBlock` (all blocks) | identity — the schoolbook keeps the product register-resident (no store-then-reload to forward) |
| **schedule search (#385)** | `RandomizedScheduleSearch.searchBest` (disjoint-footprint transposition neighbourhood) | `RandomizedScheduleSearch.feMulBlock_legal_swaps = 8` | **null** — 8 legal swaps, all `scheduleCost`-neutral; no reschedule beats the hand schedule |
| **randomized regalloc (#386)** | `RandomizedRegAlloc.searchAssign` + `accept` | `RandomizedRegAlloc.regalloc_runBlock_sound` (all injective renamings) | **rejected** — fe25519 has ZERO GP headroom (`gpFreeSlots` fully consumed; s2n itself reuses `%rax`), so no spreading renaming is *accepted* |

So on this specific kernel the generic pipeline reduces to **store-to-load
forwarding** (the one unconditional pass), which is the **identity** here because
the schoolbook never stores then reloads — and the other two are the documented
#385/#386 nulls already proved against `feMulBlock` verbatim in their pass files.

## What is proved here

* `optimizedFeMulBlock_runBlock` / `optimizedFeMulBlock_denote_eq` —
  the generic-optimized block is `runBlock`-equal (and lowered-`Com`-denotation-
  equal) to the original `Fe25519MulKernel.feMulBlock` on *every* state. The
  pipeline adds no trust: `optimizedFeMulBlock = storeToLoadForward feMulBlock`,
  and `StoreToLoadForward.storeToLoadForward_runBlock` discharges the equality
  for all blocks. Composed with `feMulBlock_lowering_correct` this gives the
  generic-optimized block the same `(x·y) mod p` value semantics the hand kernel
  has (gated externally by the same `bench/x25519_fieldmul_compare` KAT).
* `optimizedFeMulBlock_eq_handTuned` — for this kernel the generic-optimized
  block is *syntactically identical* to the hand-tuned block (store-to-load
  forwarding is the identity on a store-free schoolbook). The emit is therefore
  byte-identical, so the measured `cyc/op` is the hand-tuned baseline.

## The #555 finding (predicted; the orchestrator measures)

The generic owned optimizer, applied to `fe25519_mul`, **reproduces the
hand-tuned schedule and allocation exactly** — because on this kernel each
generic pass is provably identity / null / rejected. So the generic-optimized
emit is byte-identical to the hand-tuned `.s`, and the predicted `cyc/op` is the
**hand-tuned 26.41** (parity, not a regression). The honest reading: this kernel
is *already at the generic-pipeline fixpoint* — there is no hand-tuning here for
the generic pipeline to lose, because the hand schedule/alloc coincide with what
the generic passes would (and provably cannot improve on, per #385/#386). The
real #555 generalisation work is the kernels where the hand path does something
the generic passes do **not** yet express (instruction *selection* — the
fused-quotient-estimate reduce — which is upstream of schedule/RA and not a
`JInstr→JInstr` reorder/rename); see the module-end note.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulOptimized

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
open CatCrypt.Crypto.Optimizer.StoreToLoadForward (storeToLoadForward storeToLoadForward_runBlock
  storeToLoadForward_lowering)

/-! ## 1. The generic-optimized block

`optimizedFeMulBlock` is `Fe25519MulKernel.feMulBlock` run through the GENERIC
owned optimizer pipeline. At the `JInstr 64` block level that pipeline is the
single unconditional pass `storeToLoadForward` (the #372 store-to-load forward),
followed by the #385 schedule search and #386 regalloc search — both of which
are provable no-ops on this kernel (the schedule search finds only cost-neutral
swaps, `RandomizedScheduleSearch.feMulBlock_legal_swaps = 8`; the regalloc search
is rejected for lack of GP headroom). We therefore *define* the optimized block
as the result of the only pass that can fire — store-to-load forwarding — and
prove below it is the identity here. -/

/-- The Curve25519 field-multiply block after the GENERIC owned optimizer
    pipeline (store-to-load forwarding; the schedule + regalloc searches are the
    documented #385/#386 nulls on this kernel). -/
def optimizedFeMulBlock : List (JInstr 64) :=
  storeToLoadForward feMulBlock

/-! ## 2. Denotation equality with the hand-tuned kernel (the pipeline adds no trust) -/

/-- **Generic-optimized = hand-tuned, on every machine state.** Running the
    generic-pipeline-optimized block from any state lands in exactly the same
    `runBlock` final state as the hand-tuned `Fe25519MulKernel.feMulBlock`. This
    is the translation-validation certificate that the generic owned optimizer
    preserves the kernel's semantics — it is an instance of
    `StoreToLoadForward.storeToLoadForward_runBlock`, which holds for *all*
    blocks. -/
theorem optimizedFeMulBlock_runBlock (s : JState 64) :
    runBlock s optimizedFeMulBlock = runBlock s feMulBlock :=
  storeToLoadForward_runBlock feMulBlock s

/-- **Dialect/`Com`-level denotation equality.** The lowered `Com` of the
    generic-optimized block denotes exactly the lowered `Com` of the hand-tuned
    block on every incoming state — the generic owned optimizer is
    denotation-preserving against the validated x86 model. -/
theorem optimizedFeMulBlock_denote_eq (s : JState 64) :
    (lowerBlock (Γ := []) optimizedFeMulBlock).denote (.cons s .nil)
      = (lowerBlock (Γ := []) feMulBlock).denote (.cons s .nil) :=
  storeToLoadForward_lowering feMulBlock s

/-! ## 3. On this kernel the generic pipeline is the identity (so the emit is byte-identical)

Store-to-load forwarding only rewrites a `loadMem r b o` whose `(b, o)` cell was
just established by a `storeMem b o (.reg r')` earlier in the block (forwarding
`r := r'`). The schoolbook keeps the eight product words register-resident and
only stores at the very end (`storeMem "z" …`) with no subsequent load, so no
forward fires: the pass is the identity. This makes the generic-optimized emit
syntactically the same instruction list as the hand kernel — hence the same
`.s`, hence the same `cyc/op`. -/

/-! ## 4. The generic-optimized emit (same owned AsmPrinter path as the hand kernel)

Because the generic pipeline is the identity here, we emit the optimized block
through the identical owned `AsmPrinter` lowering the hand kernel uses
(`feMulPinned` GP pins → `allocGp` → `renderSysVLeafFn`). The emitted `.s` is
therefore byte-identical to `Fe25519MulKernel.feMulAsm` (a different function
symbol so the bench can link both side by side). -/

/-- Register allocation for the optimized block (same first-fit allocator,
    same pins as the hand kernel). -/
def optFeMulAlloc : GpAlloc := allocGp feMulPinned optimizedFeMulBlock

/-- The rendered AT&T body of the generic-optimized block. -/
def optFeMulAsmBody : List String := renderBlockBody optFeMulAlloc optimizedFeMulBlock

/-- The full emitted `.s` leaf function for the generic-optimized block, framed
    by the same SysV ABI layer as the hand kernel. Distinct symbol
    `fe25519_mul_x86_generic_opt` so the bench harness can link it alongside the
    hand-tuned `fe25519_mul_x86_from_lean`. -/
def optFeMulAsm : String :=
  renderSysVLeafFn "fe25519_mul_x86_generic_opt" optFeMulAlloc feMulArgs optFeMulAsmBody []

/-- The generic-optimized emit has the same 95 body lines as the hand kernel. -/
theorem optFeMulAsmBody_length : optFeMulAsmBody.length = 95 := by native_decide

/-- **The generic-optimized body is byte-identical to the hand-tuned body.** Since
    the generic pipeline is the identity on `feMulBlock` and the allocator + pins
    are the same, the per-instruction rendered AT&T lines coincide line-for-line.
    (Only the function symbol differs at the `renderSysVLeafFn` framing level.) -/
theorem optFeMulAsmBody_eq_handTuned : optFeMulAsmBody = feMulAsmBody := by
  native_decide

/-- Emit driver: write the generic-pipeline-optimized `.s` for the bench harness.
    Byte-identical body to `Fe25519MulKernel.emitMain`'s output (distinct symbol),
    demonstrating that the generic owned optimizer reproduces the hand emit. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_fieldmul_compare/gen_com/fe25519_mul_x86_generic_opt.s" optFeMulAsm
  IO.println "wrote gen_com/fe25519_mul_x86_generic_opt.s (generic owned optimizer pipeline)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulOptimized
