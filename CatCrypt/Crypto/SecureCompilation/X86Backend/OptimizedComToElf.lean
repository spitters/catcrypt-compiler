/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-!
# An OPT-IN optimized `Com → owned-x86 → ELF` path (P1 activation)

This is the opt-in bridge for the P1 activation item: a
`Com → owned-x86 → ELF` route that runs the `Lprog`
body through the JInstr block-optimization passes (`composeValidated
defaultValidatedPipeline`), **without** touching the existing generic driver
`CompileComToElf.compileComToElf`. All committed output and KATs of that path are
untouched — this is a new, separate function that a caller may opt into.

## The bridge

The existing driver runs `Com.toLprogPhysAbi → LprogBytes.encodeLprog` over the
`Lprog`/`Linstr` IR with **no** block optimization. The perf passes operate on
`List (JInstr 64)`. This module wires them together:

```
Lprog body  →  List (JInstr 64)   (gatherJBlock, via LoweringExtended.lowerLinstrExtL)
            →  validated passes    (composeValidated defaultValidatedPipeline)
            →  bytes               (ScalarEncoder.encodeJBlock)
            →  ByteArray           (CompileComToElf.bytesToByteArray)
```

## The safety invariant: never silently emit wrong bytes

`gatherJBlock` lowers each `Linstr` via `LoweringExtended.lowerLinstrExtL`, which
returns `none` for every shape outside its coverage. `gatherJBlock` uses
`List.mapM`, so **one** uncovered instruction makes the whole gather `none`, and
the whole optimized path returns `none`. The caller then falls back to the
existing `compileComToElf`. There is no partial / silently-truncated emission.

## Scope notes

* `lowerLinstrExtL` covers the **reg-arith** ALU/`MOV` fragment
  (`ADD/SUB/MUL/AND/OR/XOR/SHL/SHR/MOV`) plus **constant-offset** `LOAD`/`STORE`
  (`[base + off]`, the direct-addressing mode). It returns `none` for spill /
  frame operands (`k.N` / `qsave.X` / `mem.*`), control flow
  (`Lgoto`/`Lcond`/`Lcall`/`Lret`/`Llabel`/`Lalign`), the BMI2/ADX trio
  (`MULX`/`ADCX`/`ADOX`), register-indexed memory, casts, and every other shape.
  Most real owned-emit kernels use spill traffic and a frame, so they currently
  **fall back** to the un-optimized path; this opt-in route handles the
  spill-free, frame-free, straight-line reg-arith + const-offset-memory fragment.
* The existing path / its bytes are **unchanged** (byte-safe): nothing here edits
  `compileComToElf`, `encodeLprog`, or any committed driver.
* Semantics are preserved by `X86OptPipelineComposed.composeValidated_sound` (an
  unconditional `runBlock`-equality between the optimized and the gathered block),
  exposed here as `optimizedJBlock_sound`. The optimized **bytes**, however,
  differ from `encodeLprog`'s, so a per-kernel byte-KAT is required before a
  kernel adopts this path.
* Flipping the *default* to this route is a later step, gated on that per-kernel
  byte-KAT verification and (for spill coverage) extending `lowerLinstrExtL` to
  the spill/frame operand shapes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf (bytesToByteArray)

/-! ## 1. Gathering an `Lprog` body into a `JInstr` block (the coverage guard) -/

/-- Lower an `Lprog` function body to a `List (JInstr 64)`, mapping each `Linstr`
    through `LoweringExtended.lowerLinstrExtL` and **flattening** the per-instruction
    blocks. `List.mapM` over `Option` means a single uncovered instruction (spill /
    frame / control-flow / BMI2-ADX / indexed-memory shape — anything
    `lowerLinstrExtL` drops) makes the WHOLE gather `none`. This is the
    no-silent-wrong-bytes guard: the optimized path only succeeds on a body whose
    every instruction is in the `lowerLinstrExtL` fragment. -/
def gatherJBlock (body : List Linstr) : Option (List (JInstr 64)) :=
  (body.mapM lowerLinstrExtL).map List.flatten

/-! ## 2. The optimized block

The placement parameters of `defaultValidatedPipeline` (`prot`/`pinned`/`frameBase`/
`spillBase`) are the per-driver choices; for this straight-line, spill-free fragment
we use the empty/zero placement (no protected footprint, no pinned registers, frame
base `0`, spill base `%rbp`) — the same instantiation the
`X86OptPipelineComposed.demoPipeline` uses. Only **store-to-load forwarding** carries
a content-bearing certificate in that pipeline; the register-allocation and mem2reg
passes are no-op-gated, so on this fragment the pipeline is store-to-load forwarding
plus two certified no-ops. -/

/-- The validated optimizer pipeline instantiated for this opt-in route. -/
def optPipeline : List ValidatedPass :=
  defaultValidatedPipeline [] [] 0 "%rbp"

/-- Gather an `Lprog` body to a `JInstr` block and run the validated passes
    (`composeValidated optPipeline`). `none` iff any instruction is outside the
    `lowerLinstrExtL` fragment. -/
def optimizedJBlock (body : List Linstr) : Option (List (JInstr 64)) :=
  (gatherJBlock body).map (composeValidated optPipeline)

/-! ## 3. Soundness: the optimization preserves the gathered block's semantics

`optimizedJBlock_sound` is a direct instance of
`X86OptPipelineComposed.composeValidated_sound` (the unconditional `runBlock`-equality
of the validated pipeline): whenever the gather succeeds (`gatherJBlock body = some g`)
and the optimized block is its pipeline output (`optimizedJBlock body = some opt`), the
optimized block lands in the same `runBlock` final state as the gathered block on
EVERY machine state. The opt-in route is therefore semantically equivalent to the
un-optimized JInstr lowering of the same body. -/

/-- **Soundness.** When `gatherJBlock body = some g` and `optimizedJBlock body = some opt`,
    the optimized block is `runBlock`-equal to the gathered block on every state. -/
theorem optimizedJBlock_sound (body : List Linstr) (g opt : List (JInstr 64))
    (hg : gatherJBlock body = some g) (ho : optimizedJBlock body = some opt) :
    ∀ s : JState 64, runBlock s opt = runBlock s g := by
  intro s
  have hopt : opt = composeValidated optPipeline g := by
    unfold optimizedJBlock at ho
    rw [hg] at ho
    simpa using ho.symm
  subst hopt
  exact composeValidated_sound optPipeline g rfl s

/-- **Footprint-relative soundness.** The general form of `optimizedJBlock_sound`:
    the optimized block agrees with the gathered block modulo the pipeline's
    accumulated dead set `composedDead optPipeline g` on every state. For this
    pipeline that dead set is `[]`, so this specializes to the full-state
    `optimizedJBlock_sound`. An instance of `composeValidated_sound_fp`. -/
theorem optimizedJBlock_sound_fp (body : List Linstr) (g opt : List (JInstr 64))
    (hg : gatherJBlock body = some g) (ho : optimizedJBlock body = some opt) :
    ∀ s : JState 64,
      agreeExcept (composedDead optPipeline g) (runBlock s opt) (runBlock s g) := by
  intro s
  have hopt : opt = composeValidated optPipeline g := by
    unfold optimizedJBlock at ho
    rw [hg] at ho
    simpa using ho.symm
  subst hopt
  exact composeValidated_sound_fp optPipeline g s

/-- **Constant-time preservation.** When `gatherJBlock body = some g` and the gathered
    block is in the direct-addressing constant-time class (`allDirect g = true`), the
    optimized block is too. An instance of `composeValidated_allDirect`. -/
theorem optimizedJBlock_allDirect (body : List Linstr) (g opt : List (JInstr 64))
    (hg : gatherJBlock body = some g) (ho : optimizedJBlock body = some opt)
    (hd : allDirect g = true) : allDirect opt = true := by
  have hopt : opt = composeValidated optPipeline g := by
    unfold optimizedJBlock at ho
    rw [hg] at ho
    simpa using ho.symm
  subst hopt
  exact composeValidated_allDirect optPipeline g hd

/-! ## 4. Encoding the optimized block to ELF bytes

The optimized `JInstr` block is byte-encoded by `ScalarEncoder.encodeJBlock` under the
**identity allocation** (`[]` `GpAlloc`): the body registers gathered by
`lowerLinstrExtL` are already the physical names the kernel allocation pinned, so the
allocation is name-as-itself, exactly as `LprogBytes`'s straight-line bridge resolves
them. The flat byte stream is wrapped to a `ByteArray` by `CompileComToElf.bytesToByteArray`.

Scope: this emits the **flat `.text` bytes** of the optimized block (the straight-line
fragment has no control flow, no spill frame, no callee-saved push/pop), suitable for a
single-function leaf. A kernel that needs the full ABI framing (prologue/epilogue/frame)
is outside the `lowerLinstrExtL` fragment and is gathered to `none`, so it never reaches
here — it falls back to the existing path. -/

/-- Encode an optimized `JInstr` block to a flat-`.text` `ByteArray` under the identity
    allocation. -/
def encodeOptBlock (opt : List (JInstr 64)) : ByteArray :=
  bytesToByteArray (encodeJBlock ([] : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc) opt)

/-- **Opt-in `Lprog → ELF bytes`.** Extract the FIRST function's body (the
    single-function case the straight-line fragment targets), optimize it, and encode
    it to flat-`.text` bytes. Returns `none` if the `Lprog` has no function, or if any
    instruction in the body is outside the `lowerLinstrExtL` fragment (so the caller
    falls back to `compileComToElf`). A multi-function `Lprog` uses only its first
    function here; a kernel that needs multiple emitted functions is outside
    this opt-in route's single-leaf scope. -/
def optimizedLprogToElf (p : Lprog) : Option ByteArray :=
  match p.lp_funcs with
  | [] => none
  | (_, fd) :: _ => (optimizedJBlock fd.lfd_body).map encodeOptBlock

/-- **Opt-in `Com → ELF bytes`.** `Com.toLprogPhysAbi` (same parameter list as
    `CompileComToElf.compileComToElf`) then `optimizedLprogToElf`.

    `some bytes` = optimized bytes (the caller may use them after a per-kernel byte-KAT);
    `none` = the body is outside the `lowerLinstrExtL` fragment (or has no function), so
    the caller falls back to the existing, UNCHANGED `compileComToElf`. -/
def optimizedCompileComToElf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0) : Option ByteArray :=
  optimizedLprogToElf (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence abiW)

/-! ## 5. Worked demo: a body fully covered by `lowerLinstrExtL`

`demoBody` is a small straight-line body in the `lowerLinstrExtL` fragment: a couple of
reg-arith ops plus a const-offset `LOAD` and `STORE`. Every instruction lowers, so
`gatherJBlock` and `optimizedJBlock` both succeed, and `optimizedLprogToElf` /
`optimizedCompileComToElf` (via a one-function `Lprog`) return `some <bytes>`. The
soundness theorem is instantiated on this body. -/

/-- A small straight-line body, every instruction in the `lowerLinstrExtL` fragment:
    `LOAD t := a[0]`, `ADD t += b`, `MOV c := t`, `STORE r[1] := c`. -/
def demoBody : List Linstr :=
  [ ⟨0, .Lopn [.reg "t"] "LOAD"  [.arr "a" 0]⟩,
    ⟨0, .Lopn [.reg "t"] "ADD"   [.reg "b"]⟩,
    ⟨0, .Lopn [.reg "c"] "MOV"   [.reg "t"]⟩,
    ⟨0, .Lopn [.reg "r"] "STORE" [.arr "r" 1, .reg "c"]⟩ ]

/-- The gather succeeds on `demoBody` (every instruction is covered): a four-element
    `JInstr` block (one per `Linstr`). -/
theorem demoBody_gather :
    gatherJBlock demoBody
      = some [ .loadMem "t" "a" (0 : Int),
               .add "t" (.reg "b"),
               .mov "c" (.reg "t"),
               .storeMem "r" (1 : Int) (.reg "c") ] := rfl

/-- The optimized block also succeeds on `demoBody` (the pipeline is total). -/
theorem demoBody_optimized_isSome :
    (optimizedJBlock demoBody).isSome = true := rfl

/-- A one-function `Lprog` wrapping `demoBody`. -/
def demoLprog : Lprog :=
  { lp_funcs := [("demo", { lfd_body := demoBody })] }

/-- **`optimizedLprogToElf demoLprog` returns `some <bytes>`** — the opt-in path
    produces optimized ELF bytes for a fully-covered body. -/
theorem demo_lprog_isSome : (optimizedLprogToElf demoLprog).isSome = true := rfl

/-- **Soundness instantiated on the demo.** The optimized demo block is
    `runBlock`-equal, on every state, to the gathered demo block. -/
theorem demo_sound (g opt : List (JInstr 64))
    (hg : gatherJBlock demoBody = some g)
    (ho : optimizedJBlock demoBody = some opt) :
    ∀ s : JState 64, runBlock s opt = runBlock s g :=
  optimizedJBlock_sound demoBody g opt hg ho

/-- A small concrete byte check: the optimized demo block encodes to a NON-EMPTY flat
    `.text` byte stream (the encoder produced real instruction bytes for the covered
    fragment). -/
theorem demo_bytes_nonempty :
    (optimizedLprogToElf demoLprog).any (fun ba => ba.size > 0) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
