/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ComToArithBlock
public import CatCrypt.Crypto.SecureCompilation.Ascent.FreshForCheck
public import CatCrypt.Crypto.SecureCompilation.Ascent.BlockContextSynthesis

/-!
# A dialect program, its bytes, and its value

A `Com jasminDialect` that `comToArithBlock` recognises lowers to a machine
block, encodes to a byte string, decodes back to that block, and leaves the
program's denotation in the output register.

## What is proved

* `dialect_bytes_denote` — the composition over an arbitrary recognised program,
  a register map and a fresh allocation: the encoding decodes to the lowered
  block renamed through the allocation, and running the block leaves
  `c.denote V` in the output register.
* `bytesOfCom` / `demo_bytes_decode` / `demo_bytes_denote` — the instance. The
  two-operation program `let s1 = x + y in let s2 = s1 * x in ret s2` lowers to
  six instructions over `%rax`, `%rbx`, `%rcx` and `%rdx`, and its bytes decode
  back to those instructions and compute `(x + y) * x`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-! ## 1. The composition -/

/-- **A recognised dialect program reaches bytes and keeps its value.** For a
    `Com jasminDialect` that `comToArithBlock` recognises, a register map
    corresponding to the valuation and a fresh allocation, the encoding of the
    lowered block decodes to that block renamed through the allocation, and the
    output register after `runBlock` holds the program's denotation. -/
theorem dialect_bytes_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (ab : ArithBlock Γ)
    (h : comToArithBlock c = some ab)
    (nm : RegMapG Γ) (g : Nat → String) (alloc : GpAlloc)
    (hc : ∀ i ∈ lowerBlock ab nm g, blockCovered i = true)
    (hr : ∀ i ∈ lowerBlock ab nm g, mulxRdxOk alloc i = true)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm g)
    (hmem : BlockMemOk ab nm g V s := by first | trivial | simp [BlockMemOk]) :
    decodeJStream (lowerBlock ab nm g).length
        (encodeJBlock alloc (lowerBlock ab nm g))
        = some ((lowerBlock ab nm g).map (renameJ alloc))
      ∧ (runBlock s (lowerBlock ab nm g)).get (outReg ab nm g) = c.denote V :=
  ⟨roundtrip_block alloc (lowerBlock ab nm g) hc hr,
   com_lowerBlock_runBlock c ab h nm g s V hinterp hfresh hmem⟩

/-! ## 2. The register map and the destination stream of the instance -/

/-- The register map for `comBlock2`: the first input in `%rax`, the second in
    `%rbx`. -/
def nm2 : RegMapG Δ2 := fun v =>
  match v with
  | .here => "%rax"
  | .there .here => "%rbx"

/-- The destination stream: `%rcx` for the first result, `%rdx` for the second,
    and padding names beyond. -/
def g2 : Nat → String := fun i =>
  match i with
  | 0 => "%rcx"
  | 1 => "%rdx"
  | k + 2 => padName k

/-- The four register names of the instance are not padding names. -/
theorem rdx_ne_padName (k : Nat) : ("%rdx" : String) ≠ padName k :=
  ne_padName_of_second _ 'r' ['d', 'x'] (by decide) (by decide) k

/-- The allocation of the instance is fresh: the two destinations are distinct,
    neither is a padding name or an input register, and the padding names are
    distinct from each other. -/
theorem g2_fresh : FreshFor nm2 g2 := by
  constructor
  · intro i j hij
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, 1 => exact by decide
    | 1, 0 => exact by decide
    | 1, 1 => exact absurd rfl hij
    | 0, j + 2 => exact rcx_ne_padName j
    | 1, j + 2 => exact rdx_ne_padName j
    | i + 2, 0 => exact fun hp => rcx_ne_padName i hp.symm
    | i + 2, 1 => exact fun hp => rdx_ne_padName i hp.symm
    | i + 2, j + 2 =>
        exact fun hp => hij (by rw [padName_inj hp])
  · intro i v
    match i, v with
    | 0, .here => exact by decide
    | 0, .there .here => exact by decide
    | 1, .here => exact by decide
    | 1, .there .here => exact by decide
    | i + 2, .here => exact fun hp => rax_ne_padName i hp.symm
    | i + 2, .there .here => exact fun hp => rbx_ne_padName i hp.symm

/-! ## 3. The instance -/

/-- The machine block the two-operation program lowers to. -/
def demoBlock : List (JInstr 64) := lowerBlock block2 nm2 g2

/-- The bytes of that block under the identity allocation. -/
def bytesOfCom : List (BitVec 8) := encodeJBlock idAlloc demoBlock

/-- The bytes decode back to the block they encode. -/
theorem demo_bytes_decode :
    decodeJStream demoBlock.length bytesOfCom = some demoBlock := by
  rw [bytesOfCom, roundtrip_block idAlloc demoBlock (by decide) (by decide)]
  rfl

/-- Running the decoded block leaves the two-operation program's denotation in
    `%rdx`, for every machine state corresponding to the valuation. -/
theorem demo_bytes_denote (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpG nm2 V s) :
    (runBlock s demoBlock).get "%rdx" = comBlock2.denote V := by
  have h := com_lowerBlock_runBlock comBlock2 block2 comBlock2_recognise nm2 g2
    s V hinterp g2_fresh
  rwa [show outReg block2 nm2 g2 = "%rdx" from rfl] at h

/-! ## 4. Non-vacuity

The hypothesis is satisfiable and both sides evaluate to a value. -/

/-- The valuation `⟨7, 35⟩`. -/
def sampleV2 : Ctxt.Valuation Δ2 := .cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil)

/-- A machine state holding that valuation in `%rax` and `%rbx`. -/
def sampleS2 : JState 64 :=
  { regs := fun r => if r = "%rax" then 7 else if r = "%rbx" then 35 else 0 }

/-- The state corresponds to the valuation. -/
theorem sampleS2_interp : JStateInterpG nm2 sampleV2 sampleS2 := by
  intro v
  match v with
  | .here => rfl
  | .there .here => rfl

/-- On the concrete state the block leaves `(7 + 35) * 7 = 294` in `%rdx`. -/
theorem sample_dialect_bytes :
    (runBlock sampleS2 demoBlock).get "%rdx" = (294 : BitVec 64) := by
  rw [demo_bytes_denote sampleS2 sampleV2 sampleS2_interp]
  exact comBlock2_denote_concrete

end CatCrypt.Crypto.SecureCompilation.Ascent
