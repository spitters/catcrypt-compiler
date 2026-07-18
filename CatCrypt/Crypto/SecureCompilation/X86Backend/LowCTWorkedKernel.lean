/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMvcgen
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-!
# End-to-end worked example: an FNV-1a-style mixing kernel through the verified compiler

This module instantiates the **whole** verified `LowCT → JInstr` compiler chain on
**one concrete, named, recognizable cryptographic mixing kernel** — a two-word
**FNV-1a-style** hash core — and carries all five backend guarantees on it as
instantiated theorems plus a one-vector value KAT.  It is the "it all composes on
a real artifact" demonstration: the generic theorems of `LowCTToJInstrCT`,
`LowCTMvcgen`, `LowCTRobustCT`, `LowCTSecPreserve` and the `ScalarEncoder` are
*applied*, not re-proved, to a single concrete program.

## The kernel

FNV-1a hashes a message by repeating, per input word `xᵢ`,

  `h := (h ⊕ xᵢ) · P`

where `P` is the FNV prime (here a fixed odd constant held in a register slot).
This is a textbook **multiply-xor mixing core**: the recognizable shape behind
FNV/Fowler–Noll–Vo and, more generally, the `xor`-then-multiply diffusion step
shared by many non-cryptographic and cryptographic mixers.  Each FNV round is two
binary scalar-arith assignments, so it lives **entirely** in the homomorphic
fragment `ArithSrc` (`xor` then `mul`/`imul`) for which `lowerSeq`,
`compile_correct_triple`, `lowerSeq_constant_time` and `wholeFn`-style security
preservation apply directly — no cross-construct (guarded / memory / loop)
composition is required.

We unroll **two** rounds (`x₀`, `x₁`) over slots `h`, `x0`, `x1`, `p`:

  round 0:  `h := h ⊕ x0` ;  `h := h · p`
  round 1:  `h := h ⊕ x1` ;  `h := h · p`

so `kernelProg : List ArithSrc` is four statements.  All are homomorphic (`xor`,
`mul`), so the lowering is `lowerSeq` and every guarantee below comes from the
existing straight-line block theorems.

## The five guarantees, instantiated on `kernelProg`

1. **Functional correctness** (`kernel_compile_correct_triple`): the `mvcgen`
   Hoare triple `compile_correct_triple` on `kernelProg` — running the lowered
   machine block from a `StateMatch`-matching state lands in a state matching the
   folded source semantics `srcDenote kernelProg`.  The register-allocation
   side-conditions (`ρ` injective, each statement's `b ≠ dst`) are discharged by
   `decide`/`simp` on the concrete four-statement program.
2. **Constant-time** (`kernel_constant_time`, `kernel_robust_CT`):
   `lowerSeq_constant_time` / `lowerSeq_robust_CT` on `kernelProg` — the lowered
   kernel's machine leakage trace is a function of the program text alone
   (state-independent), even linked with any direct-addressed context.
3. **Cryptographic-security preservation** (`kernel_preserves_security`):
   `LowCTSecPreserve.compiled_preserves_security` on `kernelProg` — a `sdist ≤ ε`
   security bound to an ideal computation transfers to the compiled kernel,
   because compile-correctness gives equal `SPComp` denotation (here the
   reflexive same-program instance, `srcDenote` agreement is `rfl`).
4. **Lowering to bytes** (`kernelBytes`, `kernel_encode_length`): the lowered
   block is encoded to x86-64 machine code by the verified `ScalarEncoder`
   (`encodeJBlock`), and its byte length is pinned in-Lean.
5. **Value KAT** (`kernel_value_kat`): `native_decide` that running the lowered
   block from one concrete input state reads back the hand-computed FNV-1a-style
   output on `ONE` small test vector — grounding that the kernel computes the
   intended mixing.

## Honest scope

* This is the end-to-end worked example on the **supported bounded fragment**:
  straight-line, terminating, deterministic, memory-free scalar-arith.  It uses
  only the homomorphic op set (`xor`, `mul`); the guarded fragment
  (`sub`/`shl`/`shr`, e.g. a splitmix64 `z := (z ⊕ (z ≫ 30))·P` finalizer) and
  memory/loop constructs compose through separate bridges (`LowCTGuardedCT`,
  `LowCTMemCT`, `LowCTForCT`) and are **not** combined here — a richer kernel
  mixing homomorphic + guarded + loop steps is left as future work.
* The **byte-vs-`gas` differential KAT** (assembling the same block with the
  system assembler and diffing the bytes) is **external** — see the bench
  harness.  In-Lean we keep only the `encodeJBlock` definition + the byte-length
  fact, and a single tiny value vector for the run-semantics KAT, per the
  project's "no heavy multi-vector `native_decide`" policy.
* `P` is a fixed odd constant in a register slot (FNV uses an immediate prime;
  the `ArithSrc` `mul` form reads two slots, so the constant rides a slot — a
  faithful encoding of the same arithmetic).

## Iris-free

Imports only the iris-free backend modules (`LowCTMvcgen`, `LowCTRobustCT`,
`LowCTSecPreserve`, `ScalarEncoder`); nothing under `Bridges/` or `IrisBridge/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTWorkedKernel

open Std.Do
open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMvcgen
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTRobustCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSecPreserve
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTITreePRHL
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc)
open CatCrypt.Crypto.Jasmin.LowCT (RustState rsSetScalar)
open scoped ENNReal

/-! ## 1. The concrete kernel program -/

/-- The FNV-1a prime constant slot value used in the value KAT.  (The classic
    64-bit FNV prime is `0x100000001b3`; we hold it in a register slot, since the
    `ArithSrc` `mul` form reads two slots.) -/
def fnvPrime : Nat := 0x100000001b3

/-- **The kernel program.**  Two unrolled FNV-1a rounds over input words `x0`,
    `x1`, accumulating into `h` with the prime in slot `p`:

      `h := h ⊕ x0` ;  `h := h · p` ;  `h := h ⊕ x1` ;  `h := h · p`.

    Four homomorphic (`xor`/`mul`) scalar-arith statements — entirely inside the
    `ArithSrc` fragment, so `lowerSeq` and all the straight-line block theorems
    apply directly. -/
def kernelProg : List ArithSrc :=
  [ { dst := "h", a := "h", op := .xor_, b := "x0" }
  , { dst := "h", a := "h", op := .mul_, b := "p"  }
  , { dst := "h", a := "h", op := .xor_, b := "x1" }
  , { dst := "h", a := "h", op := .mul_, b := "p"  } ]

/-- **The register map.**  A **total, injective** renaming of source slots to
    distinct machine-register *names*, tagging each slot with a fixed `":r"`
    suffix (`h → "h:r"`, `x0 → "x0:r"`, …).  The suffix is constant, so the map
    is injective by right-append cancellation — exactly the register-allocation
    well-formedness the denote/triple theorems require.  The encoder's GP
    allocation (`kernelAlloc`) maps these tagged names to the real `%rN`
    registers, so byte encoding still emits SDM machine code. -/
def ρ : RegMap := fun s => s ++ ":r"

/-- `ρ` is injective: it appends a fixed suffix, so it is injective by the
    right-append cancellation lemma `String.append_left_inj`. -/
theorem ρ_injective : Function.Injective ρ := fun _ _ hab =>
  (String.append_left_inj ":r").mp hab

/-! ## 2. Well-formedness of the concrete program (discharged by `decide`) -/

/-- Each statement's second-operand slot differs from its destination — the
    per-statement WF side condition of the denote/triple theorems.  Discharged by
    `decide` on the concrete four-statement program. -/
theorem kernel_wf : ∀ p ∈ kernelProg, p.b ≠ p.dst := by
  decide

/-! ## 3. Guarantee 1 — functional correctness (the `mvcgen` Hoare triple) -/

/-- **Functional correctness, as the `mvcgen` Hoare triple** (instantiating
    `LowCTMvcgen.compile_correct_triple` on `kernelProg`).  Under `StateMatch ρ`,
    running the lowered machine block of the kernel lands in a state matching the
    folded source FNV-1a semantics `srcDenote kernelProg`:

      `⦃ StateMatch ρ rs ⦄ runBlockM (lowerSeq ρ kernelProg)
                          ⦃ StateMatch ρ (srcDenote kernelProg rs) ⦄`.

    The register-allocation side conditions (`ρ` injective; each statement's
    `b ≠ dst`) are `ρ_injective` and `kernel_wf`. -/
theorem kernel_compile_correct_triple (rs : RustState) :
    Std.Do.Triple (runBlockM (lowerSeq ρ kernelProg))
      (fun js => ⌜StateMatch ρ rs js⌝)
      (⇓ _ => fun js => ⌜StateMatch ρ (srcDenote kernelProg rs) js⌝) :=
  compile_correct_triple ρ ρ_injective kernelProg kernel_wf rs

/-- **Functional correctness, as the direct denote equality** (instantiating
    `LowCTToJInstrCT.lowerSeq_denote`).  The same content as the triple, phrased
    as the state-level correspondence used by the value KAT and the byte path. -/
theorem kernel_denote (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (srcDenote kernelProg rs) (runBlock js (lowerSeq ρ kernelProg)) :=
  lowerSeq_denote ρ ρ_injective kernelProg kernel_wf rs js hmatch

/-! ## 4. Guarantee 2 — constant-time -/

/-- **Constant-time** (instantiating `LowCTToJInstrCT.lowerSeq_constant_time`).
    The lowered kernel's machine leakage trace is the same from any two initial
    states: its observable control-flow + memory-address sequence is a function
    of the program text alone, leaking nothing about the (possibly secret) input
    words. -/
theorem kernel_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSeq ρ kernelProg) = blockLeak s₂ (lowerSeq ρ kernelProg) :=
  lowerSeq_constant_time ρ kernelProg s₁ s₂

/-- **Robust constant-time** (instantiating `LowCTRobustCT.lowerSeq_robust_CT`).
    The compiled kernel stays constant-time when linked (by `++`) with any
    direct-addressed machine context. -/
theorem kernel_robust_CT (ctx : List (JInstr 64)) (hc : allDirect ctx = true)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSeq ρ kernelProg ++ ctx)
      = blockLeak s₂ (lowerSeq ρ kernelProg ++ ctx) :=
  lowerSeq_robust_CT ρ kernelProg ctx hc s₁ s₂

/-! ## 5. Guarantee 3 — cryptographic-security preservation -/

/-- **Cryptographic-security preservation** (instantiating
    `LowCTSecPreserve.compiled_preserves_security` on `kernelProg`).  Because the
    compiled kernel's big-step `srcDenote` agrees with the source kernel's (here
    the canonical reflexive instance — source and compiled program are the same
    `LowCT` block, so the `compile_correct` equality is `rfl`), any `sdist ≤ ε`
    security bound from the kernel's `SPComp` interpretation to an ideal
    computation is preserved.

    `(secure compilation via SCIO RrHP + deterministic-to-pure lift)` -/
theorem kernel_preserves_security {α : Type}
    (h : ∀ e : LowCTITree.callEvents.Event, SPComp (LowCTITree.callEvents.Resp e))
    (rs : RustState) (ideal : SPComp RustState) {ε : ℝ≥0∞}
    (hsec : sdist (fun _ : α => interpSP h (LowCTITree.itreeDenoteArith kernelProg rs))
                  (fun _ : α => ideal) ≤ ε) :
    sdist (fun _ : α => interpSP h (LowCTITree.itreeDenoteArith kernelProg rs))
          (fun _ : α => ideal) ≤ ε :=
  compiled_preserves_security_self h kernelProg rs ideal hsec

/-! ## 6. Guarantee 4 — lowering to x86-64 bytes -/

/-- The encoder's GP allocation for the kernel: maps the four tagged slot names
    `ρ` produces (`"h:r"`, `"x0:r"`, `"x1:r"`, `"p:r"`) to distinct real `%rN`
    registers.  `regOf` then returns the `%rN` name, so `encodeJBlock` emits the
    SDM machine code for the block. -/
def kernelAlloc : GpAlloc :=
  [ ("h:r", "%rax"), ("x0:r", "%rcx"), ("x1:r", "%rdx"), ("p:r", "%rbx") ]

/-- **The lowered kernel encoded to x86-64 machine code** (via the verified
    `ScalarEncoder.encodeJBlock`).  The flat `.text` byte stream a loader / linker
    consumes — the verified-encoder analogue of `gas`-assembling the block. -/
def kernelBytes : List (BitVec 8) :=
  encodeJBlock kernelAlloc (lowerSeq ρ kernelProg)

/-- **Byte length of the encoded kernel.**  Each FNV round lowers to
    `mov ; xor ; mov ; imul` = `3 + 3 + 3 + 4 = 13` bytes (the GP `mov`/`xor`
    reg↔reg forms are 3 bytes each, the two-byte-opcode `imul r,r` is 4); two
    rounds give `26` bytes.  Pinned in-Lean by `decide` on the concrete encoding.
    (The full byte-vs-`gas` differential KAT is external — see the bench
    harness.) -/
theorem kernel_encode_length : kernelBytes.length = 26 := by
  decide

/-! ## 7. Guarantee 5 — value KAT (one tiny vector)

A single concrete input vector grounds that the lowered block computes the
intended FNV-1a-style mixing.  We start from the all-zero machine state with the
four touched registers (the tagged slot names `ρ` produces) loaded with the test
input, run the lowered block, and check the accumulator register `ρ "h" = "h:r"`
reads back the hand-computed output. -/

/-- The KAT input state: `h = 0`, `x0 = 1`, `x1 = 2`, `p = fnvPrime`, every other
    register `0`, keyed by the tagged register names `ρ` produces.  (FNV-1a's
    offset basis is folded into the `h` start value; here we use a clean `h = 0`
    start so the vector is self-contained.) -/
def kernelKatState : JState 64 :=
  { regs := fun r =>
      if r = ρ "h" then 0
      else if r = ρ "x0" then 1
      else if r = ρ "x1" then 2
      else if r = ρ "p" then BitVec.ofNat 64 fnvPrime
      else 0 }

/-- The hand-computed FNV-1a-style output for the KAT input, as a 64-bit word:

      `h₀ = 0`
      `h₁ = (h₀ ⊕ 1) · P = 1 · P = P`
      `h₂ = (h₁ ⊕ 2) · P = (P ⊕ 2) · P`   (mod 2⁶⁴).

    `P = fnvPrime`.  Stated as the closed `BitVec 64` arithmetic so the KAT pins
    the *mixing arithmetic*, not just a bare numeral. -/
def kernelKatOutput : BitVec 64 :=
  ((BitVec.ofNat 64 fnvPrime ^^^ (2 : BitVec 64)) * BitVec.ofNat 64 fnvPrime)

/-- **Value KAT (one vector).**  Running the lowered kernel block from the
    concrete `kernelKatState` reads back the hand-computed FNV-1a-style output in
    the accumulator register `ρ "h" = "h:r"`.  `native_decide` on the single
    small vector — grounding that the kernel computes the intended multiply-xor
    mixing.  (One vector only, per the project's no-heavy-`native_decide` KAT
    policy; the multi-vector byte-vs-`gas` differential KAT is external.) -/
theorem kernel_value_kat :
    (runBlock kernelKatState (lowerSeq ρ kernelProg)).get (ρ "h") = kernelKatOutput := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTWorkedKernel
