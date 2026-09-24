/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincToLowCT
public meta import CatCrypt.Crypto.Jasmin.JincToLowCT

/-!
# Emit the imported ML-DSA leaves

Writes the owned AT&T text of the Jasmin leaves the importer translates, into
`bench/mldsa_compare/gen_com/`. `JincToCom` parses the source, `JincToLowCT`
translates it to `LowCT`, and the rolled-loop front renders it, so a source
loop stays a loop.

The artifact is the output; nothing here compares values. The rendered text is
checked where it is consumed: the bench Makefile greps it and the C harness
compares every coefficient against the reference.

```
lake exe mldsa-jinc-emit
```

## Constant time

`mldsaExpandMask_constant_time` covers the program the printer receives for the
ExpandMask leaf, after the basic-block pipeline and copy coalescing: its
address-leak trace (`JincToLowCT.RolledCT.rolledLeak`) does not depend on the
input buffer, which holds the secret seed expansion, nor on any register but the
two pointer arguments. Registers and memory evolve by `JasminLsem.lsemStep`; the
back-edge compare, which that model does not execute, is given its x86 meaning.
The statement stops at the `Lprog`: the printer, its rendering of the spill
registers as stack slots, and the byte encoding are not covered.
`expandMaskLprog_check` evaluates the public-register analysis on the compiled
program by `native_decide`. `emitLeaf` runs the same analysis and writes nothing
the analysis rejects.

## ExpandA

The ExpandA leaf stores to an output index that depends on the sampled bytes,
so the analysis rejects it. Its inputs are public: FIPS 204 computes the matrix
`A = ExpandA(ρ)` from the seed `ρ`, which is part of the public key. `main`
writes it through `emitPublicLeaf`, which runs no constant-time check and
carries no constant-time statement. The render takes the state array holding
the carried `cont`, `pos`, `ctr` in `%rdi`, the output in `%rsi`, the stream
buffer in `%rdx` and the countdown seed in `%rcx`
(`JincToLowCT.whileCarriedLprog`).

## Main definitions

* `emitLeaf`: write one leaf that passes the constant-time check, reporting its
  instruction-line count.
* `emitPublicLeaf`: write one leaf with public-data inputs, without the check.
* `expandMaskLprog`: the compiled ExpandMask leaf.
* `mldsaExpandMask_constant_time`: its address-leak trace is a function of the
  pointer arguments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MldsaJincEmit

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.Jasmin.JincToLowCT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The directory the renders are written to, relative to the workspace root the
    executable runs from. -/
def outDir : String := "bench/mldsa_compare/gen_com"

/-- An instruction line: indented and not a directive. -/
def isInstrLine (l : String) : Bool :=
  l.startsWith "\t" && !((l.drop 1).startsWith ".")

/-- The argument registers of the leaf ABIs. Each holds an array pointer or a
    public iteration count, never secret data. -/
def argRegs : List String := ["RDI", "RSI", "RDX", "RCX"]

/-- Write the render of `p` to `outDir/<file>`, reporting its instruction-line
    count. -/
def writeRender (p : Lprog) (file : String) : IO Unit := do
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt p
  IO.FS.createDirAll outDir
  let path : System.FilePath := System.FilePath.mk outDir / file
  IO.FS.writeFile path asm
  let n := ((asm.splitOn "\n").filter isInstrLine).length
  IO.println s!"mldsa-jinc-emit: wrote {path} ({n} instruction lines)"

/-- Parse `src`, compile it under `sym`, and write its render to `outDir/<file>`
    when `rolledLprogCheck argRegs` accepts the compiled program. -/
def emitLeaf (src sym file : String) : IO Unit := do
  match (parseJincFun src).toOption.bind (jfunLeafLprog sym) with
  | some p =>
      if !RolledCT.rolledLprogCheck argRegs p then
        throw (IO.userError s!"mldsa-jinc-emit: {sym} fails the constant-time check")
      writeRender p file
  | none =>
      throw (IO.userError s!"mldsa-jinc-emit: the LowCT route declined {sym}")

/-- Parse `src`, compile it under `sym`, and write its render to `outDir/<file>`
    without the constant-time check. For a leaf whose inputs are public data
    only; the written text carries no constant-time statement. -/
def emitPublicLeaf (src sym file : String) : IO Unit := do
  match (parseJincFun src).toOption.bind (jfunLeafLprog sym) with
  | some p => writeRender p file
  | none =>
      throw (IO.userError s!"mldsa-jinc-emit: the LowCT route declined {sym}")

/-- The program the owned printer receives for the ExpandMask leaf. -/
def expandMaskLprog : Option Lprog :=
  (parseJincFun mldsaExpandMaskSrc).toOption.bind (jfunLeafLprog "mldsa_expand_mask_real")

/-- The public-register analysis accepts the compiled ExpandMask leaf from its two
    pointer arguments `RDI` (output) and `RSI` (input buffer). -/
theorem expandMaskLprog_check :
    expandMaskLprog.map (RolledCT.rolledLprogCheck ["RDI", "RSI"]) = some true := by
  native_decide

/-- **Constant time of the ExpandMask leaf.** The compiled ExpandMask leaf exists,
    its render is the text `emitLeaf` writes, and every function body in it is a
    rolled counted loop whose address-leak trace (`RolledCT.rolledLeak`: the
    instructions executed, the effective address of every register-indexed load
    and store, and each back-edge direction) is the same from any two states
    that agree on the pointer registers `RDI` and `RSI`. The input buffer
    contents (the expanded seed ρ′) and every other register may differ. -/
theorem mldsaExpandMask_constant_time :
    ∃ p, expandMaskLprog = some p ∧
      (parseJincFun mldsaExpandMaskSrc).toOption.bind
          (renderJFunLeaf "mldsa_expand_mask_real")
        = some (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt p) ∧
      ∀ f ∈ p.lp_funcs, ∃ r : RolledCT.RolledShape, r.toBody = f.2.lfd_body.map (·.li_i) ∧
        ∀ (w fuel : Nat) (s₁ s₂ : CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem.Lstate w),
          RolledCT.Agree ["RDI", "RSI"] s₁ s₂ →
            RolledCT.rolledLeak r fuel s₁ = RolledCT.rolledLeak r fuel s₂ := by
  have h := expandMaskLprog_check
  cases hp : expandMaskLprog with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
      rw [hp, Option.map_some, Option.some.injEq] at h
      refine ⟨p, rfl, ?_, RolledCT.rolledLprog_pub_determined _ p h⟩
      unfold expandMaskLprog at hp
      revert hp
      cases (parseJincFun mldsaExpandMaskSrc).toOption with
      | none => simp
      | some f =>
          intro hp
          simp only [Option.bind_some] at hp
          simp [renderJFunLeaf, hp]

end CatCrypt.Crypto.Jasmin.MldsaJincEmit

open CatCrypt.Crypto.Jasmin.JincToCom in
open CatCrypt.Crypto.Jasmin.MldsaJincEmit in
/-- Write the imported leaves: ExpandMask through the constant-time check, and
    ExpandA through `emitPublicLeaf`. -/
def main : IO UInt32 := do
  emitLeaf mldsaExpandMaskSrc "mldsa_expand_mask_real" "mldsa_expand_mask_rolled.s"
  emitPublicLeaf mldsaExpandASrc "mldsa_expand_a_real" "mldsa_expand_a_rolled.s"
  return 0
