/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel

/-!
# Template kernels at the System V calling convention

The code of a region kernel keeps the System V callee-saved registers `%rbx`, `%rbp`,
`%r12`-`%r15` (`AsmPrinter.calleeSavedRegs`): the printer saves each of them into its frame
slot in the prologue of the body and restores it in the epilogue
(`ExportPhysAbi.buildPrologue`, `ExportPhysAbi.calleeSaveRestoreEpilogue`), `frameTrim`
removes the save and the restore of each one that no other instruction of the body writes
(`unwrittenSaved`), so the code saves and restores exactly the callee-saved registers the
body writes, the gate of the back half checks that shape (`restoreB`), and
`regionBack_correct` gives the restoration on every halting run. The saves sit in the frame
of the code, inside the `F` bytes its `leaq -F(%rsp), %rsp` reserves, and do not meet the red
zone below it.

The clobber check `clobOkB` reads the decoded block syntactically, so the clobber set
`ProgKernelData.check` accepts contains every callee-saved register the restores write, and
the contract of `ProgKernelData.kernel` states that set. This module states the contract of
the same code at the System V convention: `ProgKernelData.abiKernel` is the linked function
with the bytes `ProgKernelData.bytes` of `ProgKernelData.kernel` and the clobber set
`abiClob d.clob`, the clobber set of the data without the callee-saved registers. Its
theorems `ProgKernelData.meets_abi` and `ProgKernelData.linked_abi` are `ProgKernelData.meets`
(correctness and constant time of the code under the contract) and `ProgKernelData.linked`
at that record, from the same check `ProgKernelData.check` and with the same hypotheses. The
keep clause of the specification at a register outside `abiClob d.clob` comes from the
clobber check for a register that is not callee-saved, and from the restoration of
`regionBack_correct` for a callee-saved one (`calleeSpec_of_restores`,
`calleeSpec_of_regionBack_ro_saved`).

## Main definitions

* `abiClob`: a clobber set without the callee-saved registers.
* `ProgKernelData.abiKernel`, `TemplateKernelData.abiKernel`: the linked function of a kernel
  at the System V convention.

## Main statements

* `calleeSpec_of_restores`: a specification at a clobber set enlarged by registers that every
  run restores is a specification at the clobber set.
* `regionBack_restores`: every leaky run of the decoded block of a result of `regionBack` from
  its precondition ends with the callee-saved registers at their entry values.
* `clobOkB_mono`: the clobber check at a clobber set gives it at every larger set.
* `calleeSpec_of_regionBack_ro_saved`: `calleeSpec_of_regionBack_ro` at a clobber set whose
  union with the callee-saved registers passes the clobber check.
* `ProgKernelData.abiKernel_clob`, `TemplateKernelData.abiKernel_clob`: the clobber set of the
  contract is disjoint from `AsmPrinter.calleeSavedRegs`.
* `ProgKernelData.meets_abi`, `ProgKernelData.linked_abi`, `TemplateKernelData.meets_abi`,
  `TemplateKernelData.linked_abi`: the code meets the contract at the System V convention, and
  the linked function is a linked kernel of the out shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel KernelShape)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT allSecret)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (CallVar holds_entryAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem (clobOkB blockWrites
  calleeSpec_of_regionBack_ro)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys gpOk)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime)
open CatCrypt.Crypto.Hax (LinkedFn)

/-! ## 1. Specifications at a clobber set without restored registers -/

/-- **A specification at a clobber set enlarged by restored registers.** If `X` meets the
    interface `c` with the registers of `S` added to its clobber set, and every run of `X`
    from the precondition of `c` ends with each register of `S` at its entry value, then `X`
    meets `c`. -/
theorem calleeSpec_of_restores {X : CalleeRun} {c : CalleeSig} {S : List String}
    (h : CalleeSpec X { c with clob := fun x => c.clob x || S.contains x })
    (hS : ∀ s t s', c.pre s → X s t s' → ∀ x ∈ S, s'.regs x = s.regs x) :
    CalleeSpec X c where
  halts := h.halts
  rsp := h.rsp
  keep s t s' hs hX r hr := by
    by_cases hm : r ∈ S
    · exact hS s t s' hs hX r hm
    · exact h.keep s t s' hs hX r (by simp [hr, hm])
  frame := h.frame
  post := h.post
  ct := h.ct

/-- **The back half restores the callee-saved registers**: every leaky run of the decoded
    block `q` of a result of `regionBack σ a p`, from an entry state of the precondition
    `regionPre σ p`, ends with each register of `DecodedCT.calleeSaved` at its entry value
    (the restoration clause of `regionBack_correct`, at the one final state of a halting
    run). -/
theorem regionBack_restores {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) (r : DoitRegime) :
    ∀ s tr s', regionPre σ p s → runOf r q s tr s' →
      ∀ x ∈ calleeSaved, s'.regs x = s.regs x := by
  rintro s tr s' ⟨hreg, V, fuel, v, hV, hv⟩ hX
  obtain ⟨prog, s₀, hd, hh, -, -, hcs, -⟩ := regionBack_correct h s V hV hreg fuel hv
  rw [hq, Option.some.injEq] at hd
  subst hd
  obtain ⟨t₀, ht₀⟩ := halts_runL r hh
  obtain ⟨-, rfl⟩ := runL_det ht₀ hX
  exact hcs

/-- **The clobber check is monotone**: a block that passes `clobOkB` at `f` passes it at every
    `g` that holds wherever `f` does. -/
theorem clobOkB_mono {q : List RInstr} {f g : String → Bool} (h : clobOkB q f = true)
    (hfg : ∀ x, f x = true → g x = true) : clobOkB q g = true := by
  unfold clobOkB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have hx' := h x hx
  simp only [Bool.or_eq_true, beq_iff_eq] at hx' ⊢
  exact hx'.imp_right (hfg x)

/-- **The specification of a region-compiled callee at the System V convention**:
    `calleeSpec_of_regionBack_ro` at a clobber set `clob` whose union with the callee-saved
    registers `DecodedCT.calleeSaved` passes the clobber check; the callee-saved registers
    are kept by the restoration of the back half (`regionBack_restores`). -/
theorem calleeSpec_of_regionBack_ro_saved {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {P : JasminLprogExport.Lprog} {bytes : List (BitVec 8)}
    (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol}
    (hc : clobOkB q (fun x => clob x || calleeSaved.contains x) = true)
    (hro : RegionArrKeep.regionROB σ a p = true)
    (hF : RegionKernelSem.layoutFootRoB σ F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) :=
  calleeSpec_of_restores (S := calleeSaved)
    (calleeSpec_of_regionBack_ro h hq hc hro hF L hsrc hL) (regionBack_restores h hq ctRegime)

/-! ## 2. The clobber set at the System V convention -/

/-- **A clobber set at the System V convention**: the registers of `clob` other than the
    callee-saved registers `DecodedCT.calleeSaved`, the list `AsmPrinter.calleeSavedRegs`. -/
def abiClob (clob : List String) : List String :=
  clob.filter fun x => !calleeSaved.contains x

/-- No register of `abiClob clob` is callee-saved. -/
theorem not_mem_calleeSavedRegs_of_mem_abiClob {clob : List String} {x : String}
    (h : x ∈ abiClob clob) : x ∉ X86Backend.AsmPrinter.calleeSavedRegs := by
  have hx := (List.mem_filter.1 h).2
  intro hm
  have hm' : x ∈ calleeSaved := hm
  simp [hm'] at hx

/-- A register of `clob` is in `abiClob clob` or callee-saved. -/
theorem contains_abiClob_or {clob : List String} {x : String} (h : clob.contains x = true) :
    ((abiClob clob).contains x || calleeSaved.contains x) = true := by
  by_cases hm : x ∈ calleeSaved
  · simp [hm]
  · have hx : x ∈ abiClob clob :=
      List.mem_filter.2 ⟨by simpa using h, by simpa using hm⟩
    simp [hx]

/-! ## 3. Region kernels at the System V convention -/

namespace ProgKernelData

variable (d : ProgKernelData)

/-- **The linked function of a kernel at the System V convention**: the linked function
    `ProgKernelData.kernel` with its bytes `bytes h`, its layout, meaning, frame size and store
    policy, at the clobber set `abiClob d.clob`, which leaves out the callee-saved registers
    that the code restores. -/
def abiKernel (h : d.check = true) : LinkedFn :=
  LinkedFn.ofRegion d.name d.params (.arr d.nOut (.word 64)) d.sem d.sem_res d.layout d.prog
    (abiClob d.clob) d.frame (bytes h) d.post_sem d.pubWords d.pol

variable {d}

/-- **The clobber set of the kernel at the System V convention is disjoint from the
    callee-saved registers.** -/
theorem abiKernel_clob (h : d.check = true) :
    ∀ x ∈ (abiKernel d h).clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  fun _ hx => not_mem_calleeSavedRegs_of_mem_abiClob hx

/-- The entry conditions of the layout hold under the resources of every call. -/
theorem layoutRegions_of_entryAt_abi (h : d.check = true) {a : CallVar} {s : AState}
    (he : ((abiKernel d h).entryAt a).holds s) : d.layout.Regions s :=
  RegionLinkCall.regions_of_entryAt d.bounds d.regions_nodup d.regions_ro
    RegionKernel.ofRegion_frameLo d.frameHi he

/-- **The precondition of the kernel at its call sites** at the System V convention. -/
theorem callSite_regionPre_abi (h : d.check = true) :
    (abiKernel d h).CallSitePre fun vals => ((abiKernel d h).sem vals).isSome = true := by
  intro a s he hd
  refine d.regionPre_of_regions (layoutRegions_of_entryAt_abi h he) ?_
  have hv : d.layout.args.map (·.read s) = a.vals := (holds_entryAt he).2.2.1
  rw [hv]
  change (d.sem a.vals).isSome = true at hd
  simpa only [sem, Option.isSome_map] using hd

/-- **The code of the kernel meets the contract at the System V convention**: `meets` at the
    clobber set `abiClob d.clob`, from the same check. -/
theorem meets_abi (h : d.check = true) : (abiKernel d h).Meets := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_wide d.wide (wideTy_words d.nOut) (compile_eq h)
  rw [← d.backProg_eq hq] at hb
  have hspec := calleeSpec_of_regionBack_ro_saved (args := []) (res := none)
    (clob := fun x => (abiClob d.clob).contains x) hb (decode_eq h)
    (clobOkB_mono (clobOk h) fun _ hx => contains_abiClob_or hx) (regionRO h) (footRo h)
    (allSecret d.Γ)
    (fun fuel => d.backProg_eq hq ▸ VIR.NarrowWords.narrowPrep_cast_nfct (fun _ => rfl) d.wide
      (wideTy_words d.nOut) hq (d.nfct fuel))
    (pubLabelsOK_allSecret d.layout)
  rw [regionSig_congr d.layout (d.backProg_denote hq)] at hspec
  exact ofRegion_meets_of_calleeSpec (decode_eq h) hspec
    (read_entryRegs_of_sub d.result_regs)
    (fun _ _ hs => LinkedFnMeets.pre_of_callSite (callSite_regionPre_abi h) hs)
    (ofRegion_footOut d.result d.out_region d.out_fit d.wins)

/-- The parameters of the data of the kernel at the System V convention are the parameters
    of its layout. -/
theorem ins_eq_abi (h : d.check = true) {c : CalleeData}
    (hc : (abiKernel d h).calleeData = some c) : c.ins = layoutIns d.layout := by
  obtain ⟨-, -, hargs, -, -, -, -, -, -, -, -, harr⟩ := LinkedFn.calleeData_eq hc
  unfold CalleeData.ins
  rw [hargs, harr]
  rfl

/-- **The kernel at the System V convention is a linked kernel** of the out shape, with the
    destination the parameter `po` of the parameters `ins` of its layout: `linked` at the
    clobber set `abiClob d.clob`, with the same hypotheses. -/
theorem linked_abi (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (abiKernel d h) where
  res_slice := by intro t ht; cases ht
  sem_kinds := by
    intro vals v hv
    obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hv
    exact (d.ref_kinds vals r hr).trans d.kinds_eq.symm
  kinds := fun _ _ => d.kinds_eq
  arity := d.arity
  args_nodup := d.args_nodup
  frame_fit := d.frame_fit
  callSite := callSite_regionPre_abi h
  code c hc := by
    refine ⟨.out po d.nOut ?_ rfl, meets_abi h⟩
    rw [ins_eq_abi h hc, hins]
    exact outLayout_ofRegion hargs hdest (hpo ▸ d.result) hgp fun _ _ hx => by
      rw [hpo]
      exact foot hx

end ProgKernelData

/-! ## 4. Template kernels at the System V convention -/

namespace TemplateKernelData

variable (d : TemplateKernelData)

/-- **The linked function of a template kernel at the System V convention**: the
    compiled template under its layout, with the meaning `sem`, at the clobber set
    `abiClob d.clob`. -/
def abiKernel (h : d.check = true) : LinkedFn := d.toProgKernelData.abiKernel h

variable {d}

/-- **The clobber set of the template kernel at the System V convention is disjoint from the
    callee-saved registers.** -/
theorem abiKernel_clob (h : d.check = true) :
    ∀ x ∈ (abiKernel d h).clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  ProgKernelData.abiKernel_clob h

/-- **The precondition of the template kernel at its call sites** at the System V
    convention. -/
theorem callSite_regionPre_abi (h : d.check = true) :
    (abiKernel d h).CallSitePre fun vals => ((abiKernel d h).sem vals).isSome = true :=
  ProgKernelData.callSite_regionPre_abi h

/-- **The code of the template kernel meets the contract at the System V convention.** -/
theorem meets_abi (h : d.check = true) : (abiKernel d h).Meets :=
  ProgKernelData.meets_abi h

/-- **The template kernel at the System V convention is a linked kernel** of the out shape,
    with the destination the parameter `po` of the parameters `ins` of its layout. -/
theorem linked_abi (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (abiKernel d h) :=
  ProgKernelData.linked_abi h hins hargs hdest hgp hpo

end TemplateKernelData

end CatCrypt.Crypto.SecureCompilation.HashTemplate
