/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Register-indexed (`base + idx·scale`) memory addressing through the owned backend (#581)

The multivariate-signature GE-solve loops (`MAYO`/`UOV`/`SNOVA`/`QR-UOV`'s
`sample_solution`) all access a flat augmented matrix by a **runtime** cell index
`row·AC + col` that lives in a register and advances across the elimination
sweep. The owned x86 backend previously only modelled a *static-displacement*
memory operand (`off(%base)`, `JInstr.loadMem`/`storeMem`); a register-indexed
cell access had to be open-coded as a per-step pointer bump (`p += 8`). This
module exercises the new register-indexed addressing mode added to the model —
`JInstr.loadMemIdx`/`storeMemIdx`, the `mov (%base, %idx, scale), %dst` SIB form
whose effective offset is `scale · (s.get idx).toNat` computed at run time
(`JState.loadIdx`/`storeIdx`).

It builds a small GE-solve-shaped body over a flat `row·AC + col` matrix using
the indexed arms, proves its lowering denotes the bounded-loop machine semantics
for **every** trip count (an instance of `boundedLoop_lowering_denote_closed`,
no loop-running `native_decide`), and pins the `base + idx·scale` effective-cell
computation with a small KAT on a tiny matrix.

This is the single shared addressing seam the four multivariate families share;
`MAYO.SolveEmit` wires its cross-iteration cell access onto it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.IndexedAddrEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

/-! ## 1. The indexed GE-sweep step (`JInstr 64`)

One step of a flat-matrix copy sweep: read the source cell `[src + idx·8]`, write
it to the destination cell `[dst + idx·8]` (the same flat `row·AC + col` index),
advance the index register `idx` by one cell, and decrement the cell counter `n`.
The cell stride is `8` (U64-word granularity — one GF(16) nibble per word, the
same packed-row layout the multivariate KATs present). The index register is the
cross-iteration state: a single base pointer plus an advancing index,
rather than a per-step pointer bump. -/

/-- One indexed sweep step over flat cell `idx`: `[dst + idx·8] := [src + idx·8]`,
    then `idx += 1`, `n -= 1`. Uses the register-indexed SIB addressing arms. -/
def idxSweepStep : List (JInstr 64) :=
  [ .loadMemIdx "v" "src" "idx" 8        -- v := [src + idx·8]
  , .storeMemIdx "dst" "idx" 8 (.reg "v") -- [dst + idx·8] := v
  , .add "idx" (.imm 1)                   -- idx += 1  (advance one flat cell)
  , .sub "n" (.imm 1) ]                   -- n -= 1

/-! ## 2. The `base + idx·scale` effective-cell KAT (one tiny matrix)

We seed a flat `2×2` matrix (`AC = 2`, so cell `(row, col)` is at flat index
`row·2 + col`) in `src` and an empty `dst`, start the index at `0`, and run the
sweep over all four cells. The copy lands each `src` cell at the **matching**
flat `dst` index — i.e. `base + idx·scale` resolves to the right cell at every
step. We read back two representative cells through the same indexed effective
address to confirm the addressing computes `scale · idx`. -/

/-- Seed a flat `2×2` (`AC = 2`) matrix `src[0..3]` at U64 stride `8`, an empty
    `dst`, index `idx = 0`, counter `n = 4`. -/
def seedMatrix (c00 c01 c10 c11 : Nat) : JState 64 :=
  { regs := fun r => if r = "idx" then 0
                     else if r = "n" then 4 else 0
    flags := { }
    mem := fun base off =>
      if base = "src" then
        (if off = 0 then BitVec.ofNat 64 c00
         else if off = 8 then BitVec.ofNat 64 c01
         else if off = 16 then BitVec.ofNat 64 c10
         else if off = 24 then BitVec.ofNat 64 c11 else 0)
      else 0 }

/-- **Indexed effective-cell value (one tiny matrix).** Sweeping the flat `2×2`
    matrix `[[0x7, 0xb], [0x3, 0xd]]` copies every `src` cell to the matching
    `dst` flat index. Reading the cells back through the **register-indexed**
    effective address `(%dst, %idx, 8)` (the `JState.loadIdx` the model evaluates
    for the SIB form) yields exactly `8 · idx`-offset cells:
    `dst[(0,0)] = 0x7`, `dst[(0,1)] = 0xb`, `dst[(1,0)] = 0x3`, `dst[(1,1)] = 0xd`.
    The index counter is exhausted (`idx = 4`, `n = 0`). Pinned through the full
    `evalInstr`/`loadIdx`/`storeIdx` chain. -/
theorem idxSweep_effective_cell :
    let s := runBoundedLoop (seedMatrix 0x7 0xb 0x3 0xd) 4 idxSweepStep
    -- read back each flat dst cell through its own indexed effective address
    ((s.setReg "idx" 0).loadIdx "dst" "idx" 8).toNat = 0x7
      ∧ ((s.setReg "idx" 1).loadIdx "dst" "idx" 8).toNat = 0xb
      ∧ ((s.setReg "idx" 2).loadIdx "dst" "idx" 8).toNat = 0x3
      ∧ ((s.setReg "idx" 3).loadIdx "dst" "idx" 8).toNat = 0xd
      ∧ (s.get "idx").toNat = 4 ∧ (s.get "n").toNat = 0 := by
  native_decide

/-! ## 3. Runtime-N lowering correctness (denotation = `runBoundedLoop`, every `n`)

The indexed sweep lowers to `Com (x86Dialect 64)` and denotes the bounded-loop
machine semantics for **every** runtime cell count `n` — one theorem covers all
matrix sizes (`boundedLoop_lowering_denote_closed`). The body (with its indexed
SIB loads/stores) is opaque to the structural trip-count lemma, so there is **no**
loop-running `native_decide` here. -/

theorem idxSweepLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n idxSweepStep).denote (.cons s .nil)
      = runBoundedLoop s n idxSweepStep :=
  boundedLoop_lowering_denote_closed n idxSweepStep s

/-! ## 4. AT&T emission through the owned printer (SIB rendering, no jasminc) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc renderBlockBody)

/-- A fixed register allocation for the sweep: `src→%rdi`, `dst→%rsi`,
    `idx→%rdx`, `n→%rcx`, `v→%r8`. -/
def idxSweepAlloc : GpAlloc :=
  [ ("src", "%rdi"), ("dst", "%rsi"), ("idx", "%rdx"), ("n", "%rcx"), ("v", "%r8") ]

/-- The straight-line one-cell indexed sweep, rendered to AT&T `.s` lines under
    `idxSweepAlloc`. Demonstrates the SIB operand rendering `(%base, %idx, scale)`. -/
def idxSweepAsm : List String :=
  renderBlockBody idxSweepAlloc idxSweepStep

/-- The owned printer renders the register-indexed arms as AT&T SIB operands
    `(%base, %idx, scale)` — `movq (%rdi, %rdx, 8), %r8` for the gather load and
    `movq %r8, (%rsi, %rdx, 8)` for the scatter store. No `<UNALLOCATED>` /
    unhandled operand. -/
theorem idxSweepAsm_sib_shape :
    idxSweepAsm.contains "\tmovq (%rdi, %rdx, 8), %r8" = true
      ∧ idxSweepAsm.contains "\tmovq %r8, (%rsi, %rdx, 8)" = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.IndexedAddrEmit
