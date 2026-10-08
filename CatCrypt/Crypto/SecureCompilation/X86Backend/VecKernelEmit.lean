/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage

@[expose] public section

set_option autoImplicit false

/-!
# The checked emitter of a vector kernel

`emitKernel V sym inOffset nOut c inLen F inBound` runs the vector route
`VectorizeEmit.vectorizeEmit` on the straight-line scalar program `c`, parses the text it
returns, computes the block of operations `VecMach.blockOfText` of the parsed program, runs
the frame check `VecKernelSpec.framedB` at the input length `inLen` and the frame size `F`,
and checks `F < 2 ^ 31`. It returns the text when every step succeeds, and otherwise the
error of the vector route or an error naming the step that failed.

A text `emitKernel` returns therefore has a parsed program and a block of operations whose
callee `VecKernelSpec.kernelRun` meets the signature `VecKernelSpec.kernelSig`
(`emitKernel_calleeSpec`), and a processor faithful to a lawful table of vector encodings
returns from the bytes `VecKernelImage.lineBytes` of that block in a state that satisfies
the postcondition of the signature (`emitKernel_image`).

## Main definitions

* `emitKernel`: the vector route followed by the parse, the block, the frame check and the
  bound of the frame size.

## Main results

* `emitKernel_ok`: a text `emitKernel` returns is the text of `vectorizeEmit`, it parses,
  its parsed program has a block and passes the frame check, and `F < 2 ^ 31`.
* `emitKernel_calleeSpec`: the callee of the block of a text `emitKernel` returns meets
  `kernelSig`.
* `emitKernel_post`: a run of that callee from disjoint regions whose input region holds
  parameters lane-wise ends with the outputs of the scalar program in the output region.
* `emitKernel_image`: a faithful processor returns from the bytes of that block in a state
  that satisfies the postcondition, the frame and the clobber conditions of `kernelSig`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The checked emitter -/

/-- **The checked emitter of a vector kernel.** The text `vectorizeEmit V` returns for the
    scalar program `c`, returned when it parses, its parsed program has a block of
    operations, the program passes the frame check at the input length `inLen` and the
    frame size `F`, and `F < 2 ^ 31`. Otherwise the error of `vectorizeEmit`, or an error
    naming the first of the four checks that failed. -/
def emitKernel (V : VecShape) {Γ : JCtxt} {t : JasminTy} (sym : String)
    (inOffset : Nat → Nat) (nOut : Nat) (c : Com jasminDialect Γ t) (inLen F : Nat)
    (inBound : Option Nat := none) : Except String String :=
  match vectorizeEmit V sym inOffset nOut c inBound with
  | .error e => .error e
  | .ok text =>
    match parse V.mode text with
    | .error e => .error s!"emitKernel {sym}: the text does not parse: {e}"
    | .ok (prog, ro) =>
      match blockOfText V.mode ro prog with
      | none => .error s!"emitKernel {sym}: the parsed program has no block of operations"
      | some _ =>
        if framedB V.mode inLen nOut F 0 prog then
          if F < 2 ^ 31 then .ok text
          else .error s!"emitKernel {sym}: the frame size {F} is not below 2^31"
        else
          .error s!"emitKernel {sym}: the frame check fails at input length {inLen}, \
            {nOut} outputs and frame size {F}"

variable {V : VecShape} {Γ : JCtxt} {t : JasminTy} {sym : String} {inOffset : Nat → Nat}
  {nOut : Nat} {c : Com jasminDialect Γ t} {inLen F : Nat} {inBound : Option Nat}
  {text : String}

/-- **The checks behind a text of `emitKernel`.** The text is the text of `vectorizeEmit`,
    it parses to a program with a block of operations that passes the frame check, and the
    frame size is below `2 ^ 31`. -/
theorem emitKernel_ok (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    vectorizeEmit V sym inOffset nOut c inBound = .ok text ∧
      ∃ prog ro ops, parse V.mode text = .ok (prog, ro) ∧
        blockOfText V.mode ro prog = some ops ∧
        framedB V.mode inLen nOut F 0 prog = true ∧ F < 2 ^ 31 := by
  unfold emitKernel at h
  split at h
  · cases h
  · rename_i text' hv
    split at h
    · cases h
    · rename_i prog ro hp
      split at h
      · cases h
      · rename_i ops hops
        split at h
        · rename_i hfr
          split at h
          · rename_i hF
            cases h
            exact ⟨hv, prog, ro, ops, hp, hops, hfr, hF⟩
          · cases h
        · cases h

/-! ## 2. The callee contract -/

variable (r : DoitRegime)

/-- **The callee of an emitted kernel meets its signature.** When `emitKernel` returns
    `text`, the text parses to a program `prog` with data table `ro`, the program has a
    block of operations `ops`, and `kernelRun` of `ops` meets `kernelSig` at the input
    length and the frame size given to `emitKernel`. -/
theorem emitKernel_calleeSpec
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∃ prog ro ops, parse V.mode text = .ok (prog, ro) ∧
      blockOfText V.mode ro prog = some ops ∧
      CalleeSpec (kernelRun r V.mode ops) (kernelSig V inOffset inBound nOut c inLen F) := by
  obtain ⟨hv, prog, ro, ops, hp, hops, hfr, -⟩ := emitKernel_ok h
  exact ⟨prog, ro, ops, hp, hops, calleeSpec_of_parsed r V hv hp hops hfr⟩

/-- **The outputs of a run of an emitted kernel.** When `emitKernel` returns `text`, the
    text has a block of operations `ops` such that every run of `kernelRun` of `ops` from a
    state `s` with disjoint regions whose input region holds lane-wise the parameters `Vs`
    ends in a state whose output region holds lane-wise the outputs of `c` on `Vs`. -/
theorem emitKernel_post (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∃ prog ro ops, parse V.mode text = .ok (prog, ro) ∧
      blockOfText V.mode ro prog = some ops ∧
      ∀ (s : AState) (tr : List CTLeak) (s' : AState) (Vs : Nat → Ctxt.Valuation Γ),
        KernelRegions V.mode inLen nOut F s → LaneInputs V inOffset inBound Vs s →
        kernelRun r V.mode ops s tr s' → LaneOutputs V nOut c Vs s s' := by
  obtain ⟨prog, ro, ops, hp, hops, hS⟩ := emitKernel_calleeSpec r h
  exact ⟨prog, ro, ops, hp, hops, fun s tr s' Vs hreg hin hX =>
    hS.post s tr s' ⟨hreg, Vs, hin⟩ hX Vs hin⟩

/-! ## 3. The bytes of an emitted kernel -/

/-- **The processor on the bytes of an emitted kernel.** When `emitKernel` returns `text`,
    the text parses to a program with a block of operations `ops` such that, for every
    lawful table `A` and every processor faithful to it, from an entry state with disjoint
    regions whose input region holds parameters lane-wise, with any vector state, the
    processor returns from the bytes `lineBytes A frameEnc ops` in a state whose output
    region holds lane-wise the outputs of `c`, with `%rsp` restored, every register but
    `%rax` kept and every byte outside the output region and the frame kept. -/
theorem emitKernel_image (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∃ prog ro ops, parse V.mode text = .ok (prog, ro) ∧
      blockOfText V.mode ro prog = some ops ∧
      ∀ (A : VecAsm) (cpu : List (BitVec 8) → AState × VState → AState × VState → Prop),
        A.Lawful → A.Faithful r V.mode cpu →
        ∀ s : AState, (kernelSig V inOffset inBound nOut c inLen F).pre s → ∀ v : VState,
          ∃ (s' : AState) (v' : VState), cpu (lineBytes A frameEnc ops) (s, v) (s', v')
            ∧ (kernelSig V inOffset inBound nOut c inLen F).post s s'
            ∧ s'.regs "%rsp" = s.regs "%rsp"
            ∧ (∀ x, (kernelSig V inOffset inBound nOut c inLen F).clob x = false →
                s'.regs x = s.regs x)
            ∧ ∀ a, ¬ (kernelSig V inOffset inBound nOut c inLen F).foot s a →
                s'.mem a = s.mem a := by
  obtain ⟨hv, prog, ro, ops, hp, hops, hfr, hF⟩ := emitKernel_ok h
  exact ⟨prog, ro, ops, hp, hops, fun A cpu hA hFa s hpre v =>
    faithful_calleeSpec r (calleeSpec_of_parsed r V hv hp hops hfr) hFa hA
      (frameEnc_ok_of_framed hops hfr hF) s hpre v⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelEmit
