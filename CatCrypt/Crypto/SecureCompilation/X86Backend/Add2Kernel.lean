/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# A small straight-line scalar kernel emitted through the in-Lean x86 backend

This is the first *end-to-end emitted* kernel from the in-Lean x86 backend: a
two-limb (128-bit) unsigned add-with-carry, `r = a + b`, expressed as a
straight-line `JInstr 64` block, lowered through `X86Dialect.lowerBlock`
(the verified, denotation-preserving lowering, `lowerBlock_denote`), and printed
to AT&T assembly by `AsmPrinter.renderJInstr` (the thin trusted printer).

## The kernel body (verified subset)

```
add a0, b0    -- a0 := a0 + b0, CF := carry-out
adc a1, b1    -- a1 := a1 + b1 + CF, CF := carry-out
```

`a0,a1` are the limbs of `a`; `b0,b1` the limbs of `b`. After the block,
`(a1:a0)` is the 128-bit sum and `CF` is the 129th (carry-out) bit. This is a
genuine straight-line block (no loops/branches), so `lowerBlock_denote` applies.

## What is verified vs. trusted

* **Verified**: `add2Block` lowered to `Com (x86Dialect 64)` denotes to
  `runBlock add2Block` (`add2_lowering_correct`, an instance of
  `lowerBlock_denote_closed`), and the resulting machine state computes the
  128-bit sum + carry (`add2_computes_sum`, `native_decide` on a concrete input,
  pinning the semantics). `runBlock`/`evalInstr` is the differentially-validated
  transcription of Jasmin's Rocq x86 model (`TranslationValidation.lean`).
* **Trusted (thin)**: `AsmPrinter.renderJInstr` maps each `JInstr` to one AT&T
  line; `gas` assembles it; the leaf-function ABI glue (arg-in-register, store
  result, `setc` the carry) is trusted scaffolding outside the verified body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-- The two-limb add-with-carry kernel body as a straight-line `JInstr 64`
    block: `add a0,b0; adc a1,b1`. -/
def add2Block : List (JInstr 64) :=
  [ .add "a0" (.reg "b0")
  , .adc "a1" (.reg "b1") ]

/-- **Lowering correctness.** Lowering `add2Block` to `Com (x86Dialect 64)` and
    denoting it on any initial state yields exactly `runBlock` on the source
    block — the denotation-preserving step of the in-Lean backend. -/
theorem add2_lowering_correct (s : JState 64) :
    (lowerBlock (Γ := []) add2Block).denote (.cons s .nil) = runBlock s add2Block :=
  lowerBlock_denote_closed add2Block s

/-- The kernel computes the 128-bit sum + carry-out. On a concrete carrying
    input (`a = 2^128 - 1`, i.e. `a0 = a1 = 2^64-1`; `b = 1`, i.e. `b0 = 1`,
    `b1 = 0`), the result is `a0' = 0`, `a1' = 0`, `CF = 1` (the carry rippled
    all the way out). Pins the lowered-and-denoted semantics. -/
theorem add2_computes_sum :
    let s0 : JState 64 :=
      { regs := fun r => if r = "a0" then BitVec.allOnes 64
                         else if r = "a1" then BitVec.allOnes 64
                         else if r = "b0" then 1
                         else if r = "b1" then 0 else 0
        flags := { cf := some false } }
    let s := (lowerBlock (Γ := []) add2Block).denote (.cons s0 .nil)
    (s.get "a0").toNat = 0 ∧ (s.get "a1").toNat = 0 ∧ s.flags.cf = some true := by
  intro s0 s
  rw [show s = runBlock s0 add2Block from add2_lowering_correct s0]
  native_decide

/-! ## Emission: pinned ABI + printed AT&T

`add2` has System-V signature
`uint64_t add2(uint64_t *r, uint64_t a0, uint64_t a1, uint64_t b0, uint64_t b1)`,
args in `%rdi(r) %rsi(a0) %rdx(a1) %rcx(b0) %r8(b1)`. We pin the body's named
registers to the incoming arg registers so the verified body runs in place; the
prologue is empty (args already in regs); the epilogue stores `a0→r[0]`,
`a1→r[1]`, materializes the carry via `setc`, and returns. The store/`setc`/`ret`
glue is trusted scaffolding outside the verified body. -/

/-- Pin the body's named registers to the System-V argument registers. -/
def add2Alloc : GpAlloc :=
  allocGp [("a0", "%rsi"), ("a1", "%rdx"), ("b0", "%rcx"), ("b1", "%r8")] add2Block

/-- The printed AT&T `.s` text for `add2`. The middle lines (`renderBlockBody`)
    are the verified body; the rest is trusted ABI scaffolding. -/
def add2Asm : String :=
  renderLeafFn "add2"
    (prologue := [])
    (bodyLines := renderBlockBody add2Alloc add2Block)
    (epilogue :=
      [ "\tsetc %al"          -- capture carry-out (CF after the adc)
      , "\tmovzbl %al, %eax"  -- zero-extend to the uint64_t return
      , "\tmovq %rsi, (%rdi)" -- r[0] := a0'
      , "\tmovq %rdx, 8(%rdi)"-- r[1] := a1'
      , "\tret" ])

end CatCrypt.Crypto.SecureCompilation.X86Backend.Add2Kernel
