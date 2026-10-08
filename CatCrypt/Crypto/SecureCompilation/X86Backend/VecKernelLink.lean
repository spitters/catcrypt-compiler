/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelEmit

@[expose] public section

set_option autoImplicit false

/-!
# A vector kernel as a callee that carries its specification

A caller links a vector kernel through its callee specification: the scalar decoder of the
caller never reads the kernel bytes. `VecKernelCallee r m sig` is a block of operations
`ops`, a callee run `run` on the caller's machine, the specification `CalleeSpec run sig`,
and the image fact: a processor faithful to a lawful table of vector encodings that
encodes the vector instructions of the block returns from the bytes
`VecKernelImage.lineBytes A frameEnc ops`, from every entry state that satisfies the
precondition and every vector state, in the return state of a run of `run`.

## Main definitions

* `VecKernelCallee`: the spec-carrying record of a vector kernel.
* `kernelOps`: the block of operations of the parsed text of a kernel.
* `ofVecKernel`: the record of a text the checked emitter `VecKernelEmit.emitKernel`
  returns, at the signature `VecKernelSpec.kernelSig`.

## Main results

* `VecKernelCallee.image_post`: the image fact in the shape of
  `VecKernelEmit.emitKernel_image`: the return state satisfies the postcondition, restores
  `%rsp`, keeps every register outside the clobber set and every byte outside the
  footprint.
* `ofVecKernel_ops`: the block of `ofVecKernel` is the block of the parsed text.
* `VecKernelCallee.pubSummary`: the leakage summary of the callee, from `CalleeSpec.ct`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec PubSummary)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The record -/

/-- **A vector kernel as a callee that carries its specification**, under the leakage
    regime `r` and the vector mode `m`, at the signature `sig`: the block of operations
    `ops`, the callee run `run`, its specification, and the image fact. For every lawful
    table `A` that encodes the vector instructions of the block and every processor `cpu`
    faithful to it, from every entry state that satisfies the precondition and every
    vector state, the processor returns from the bytes `lineBytes A frameEnc ops` in the
    return state of a run of `run`. -/
structure VecKernelCallee (r : DoitRegime) (m : Mode) (sig : CalleeSig) where
  /-- The block of operations of the kernel. -/
  ops : List (JInstr 64 ⊕ VInstr)
  /-- The callee on the caller's machine. -/
  run : CalleeRun
  /-- The callee meets the signature. -/
  spec : CalleeSpec run sig
  /-- A faithful processor returns from the bytes of the block in the return state of a run
      of the callee. -/
  image : ∀ (A : VecAsm) (cpu : List (BitVec 8) → AState × VState → AState × VState → Prop),
    A.Lawful → A.Faithful r m cpu → BlockEncodable A ops →
    ∀ s : AState, sig.pre s → ∀ v : VState,
      ∃ (t : List CTLeak) (s' : AState) (v' : VState),
        run s t s' ∧ cpu (lineBytes A frameEnc ops) (s, v) (s', v')

namespace VecKernelCallee

variable {r : DoitRegime} {m : Mode} {sig : CalleeSig}

/-- **The processor on the bytes of a spec-carrying kernel.** For every lawful table that
    encodes the vector instructions of the block and every processor faithful to it, from
    every entry state that satisfies the precondition and every vector state, the processor
    returns from the bytes of the block in a state that satisfies the postcondition, with
    `%rsp` restored, every register outside the clobber set kept and every byte outside the
    footprint kept. -/
theorem image_post (k : VecKernelCallee r m sig) (A : VecAsm)
    (cpu : List (BitVec 8) → AState × VState → AState × VState → Prop)
    (hA : A.Lawful) (hF : A.Faithful r m cpu) (hbe : BlockEncodable A k.ops)
    (s : AState) (hpre : sig.pre s) (v : VState) :
    ∃ (s' : AState) (v' : VState), cpu (lineBytes A frameEnc k.ops) (s, v) (s', v')
      ∧ sig.post s s'
      ∧ s'.regs "%rsp" = s.regs "%rsp"
      ∧ (∀ x, sig.clob x = false → s'.regs x = s.regs x)
      ∧ ∀ a, ¬ sig.foot s a → s'.mem a = s.mem a := by
  obtain ⟨t, s', v', hX, hc⟩ := k.image A cpu hA hF hbe s hpre v
  exact ⟨s', v', hc, k.spec.post s t s' hpre hX, k.spec.rsp s t s' hpre hX,
    k.spec.keep s t s' hpre hX, k.spec.frame s t s' hpre hX⟩

/-- **The leakage summary of a spec-carrying kernel**: two runs from entry states that
    satisfy the precondition and are related by `sig.pub` have equal traces
    (`CalleeSpec.pubSummary`). -/
theorem pubSummary (k : VecKernelCallee r m sig) : PubSummary k.run sig (fun _ _ => True) :=
  k.spec.pubSummary

end VecKernelCallee

/-! ## 2. The record of an emitted kernel -/

/-- The block of operations of the parsed text of a kernel, when the text parses and its
    parsed program has a block. -/
def kernelOps (m : Mode) (text : String) : Option (List (JInstr 64 ⊕ VInstr)) :=
  match parse m text with
  | .ok (prog, ro) => blockOfText m ro prog
  | .error _ => none

variable {V : VecShape} {Γ : JCtxt} {t : JasminTy} {sym : String} {inOffset : Nat → Nat}
  {nOut : Nat} {c : Com jasminDialect Γ t} {inLen F : Nat} {inBound : Option Nat}
  {text : String}

/-- The block of a text `emitKernel` returns is the block of its parsed program. -/
theorem kernelOps_of_emitKernel
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∃ prog ro ops, parse V.mode text = .ok (prog, ro) ∧
      blockOfText V.mode ro prog = some ops ∧ kernelOps V.mode text = some ops ∧
      vectorizeEmit V sym inOffset nOut c inBound = .ok text ∧
      framedB V.mode inLen nOut F 0 prog = true ∧ F < 2 ^ 31 := by
  obtain ⟨hv, prog, ro, ops, hp, hops, hfr, hF⟩ := emitKernel_ok h
  exact ⟨prog, ro, ops, hp, hops, by simp [kernelOps, hp, hops], hv, hfr, hF⟩

/-- **The spec-carrying record of an emitted kernel.** When `emitKernel` returns `text`,
    the block is the block of the parsed text, the run is `kernelRun` of the block, the
    specification is `kernelSig` at the input length and the frame size given to
    `emitKernel`, and the image fact holds for every lawful table and faithful
    processor. -/
def ofVecKernel (r : DoitRegime)
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F) where
  ops := (kernelOps V.mode text).getD []
  run := kernelRun r V.mode ((kernelOps V.mode text).getD [])
  spec := by
    obtain ⟨prog, ro, ops, hp, hops, hk, hv, hfr, -⟩ := kernelOps_of_emitKernel h
    rw [hk, Option.getD_some]
    exact calleeSpec_of_parsed r V hv hp hops hfr
  image := by
    obtain ⟨prog, ro, ops, hp, hops, hk, hv, hfr, hF⟩ := kernelOps_of_emitKernel h
    rw [hk, Option.getD_some]
    intro A cpu hA hFa hbe s _ v
    exact faithful_kernel_total r hFa hA (frameEnc_ok_of_framed hops hfr hF) hbe s v

/-- The block of `ofVecKernel` is the block of the parsed text of the kernel. -/
theorem ofVecKernel_ops (r : DoitRegime)
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∃ prog ro, parse V.mode text = .ok (prog, ro) ∧
      blockOfText V.mode ro prog = some (ofVecKernel r h).ops := by
  obtain ⟨prog, ro, ops, hp, hops, hk, -⟩ := kernelOps_of_emitKernel h
  refine ⟨prog, ro, hp, ?_⟩
  simp only [ofVecKernel, hk, Option.getD_some]
  exact hops

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink
