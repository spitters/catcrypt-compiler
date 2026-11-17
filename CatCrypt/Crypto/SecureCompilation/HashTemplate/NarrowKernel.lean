/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernelAbi

/-!
# Narrow-width template kernels: region-compiled linked kernels over narrow words

A narrow-width kernel is a structured program `NFProg` over a context `Γ` whose words may have
width `8`, `16` or `32`, returning an array of `nOut` words of a width `w` with
`wideW w = 64`. The region back half `compileRegion` widens the program (`narrowPrep`): every
narrow word is held zero extended in a 64-bit register or a 64-bit array slot, so the layout
of the kernel reads the widened valuation `mapVal V` of a valuation `V` of `Γ`, and reads back
the result words zero extended to 64 bits (`compileRegion_correct`). The reference function of
the kernel is therefore stated on narrow words, and it is defined only on source values whose
words lie below `2 ^ w`, at which the layout reading is the widening of a narrow valuation.

The linked function of the kernel has the contract of the widened program `wideProg`, the
result of `narrowPrep` on the program, at whose regionPre-states the reading may have
arbitrary high bits. The constant-time obligation of `calleeSpec_of_regionBack_ro` is stated
at every valuation of the widened program, not only at widened valuations, so it is decided
on the widened program by the level checker `NFProg.levelCheck` at the all-secret labels
(`ctWideB`), a conjunct of the check of the kernel.

`NarrowProgKernelData` collects the data; `NarrowProgKernelData.kernel` and
`NarrowProgKernelData.abiKernel` are the linked functions of `LinkedFn.ofRegion` at the bytes
of `compileRegion` under the clobber set of the data and under its System V form `abiClob`.
`NarrowTemplateKernelData` is the instance at the embedding `NFProg.ofCom` of a straight-line
template.

## Main definitions

* `ctWideB`: the level check of the widened program at the all-secret labels.
* `NarrowLayoutData`: the symbol, parameters, layout and narrow meaning of a kernel.
* `NarrowProgKernelData`: the data of a narrow-width region kernel.
* `NarrowProgKernelData.check`: the compile, footprint, read-only, level and clobber check.
* `NarrowProgKernelData.wideProg`: the widened program `compileRegion` compiles.
* `NarrowProgKernelData.kernel`, `NarrowProgKernelData.abiKernel`: the linked functions.
* `NarrowTemplateKernelData`: the data of a narrow-width template kernel.
* `narrowFrameCheck`: `frameCheck` and `ctWideB` in one Boolean.

## Main statements

* `denVal_transTy_wide`: the source value of a widened array of narrow words.
* `NarrowProgKernelData.post_sem`: the value-level contract of the kernel.
* `NarrowProgKernelData.meets`, `NarrowProgKernelData.linked`: the code meets the contract of
  its record, and the kernel is a linked kernel of the out shape.
* `NarrowProgKernelData.meets_abi`, `NarrowProgKernelData.linked_abi`: the same at the
  System V convention.
* `NarrowProgKernelData.check_of_frameCheck`: the check from `narrowFrameCheck`.
* `NarrowTemplateKernelData.meets`, `NarrowTemplateKernelData.linked`,
  `NarrowTemplateKernelData.meets_abi`, `NarrowTemplateKernelData.linked_abi`: the same for a
  template kernel.
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
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT allSecret)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf abiValOf_unique)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (regArrCtxB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (CallVar isResRegion
  holds_entryAt)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem (clobOkB layoutFootRoB
  calleeSpec_of_regionBack_ro)
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (narrowPrep wideTy wideW transTy mapVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep (regionROB)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys gpOk)
open CatCrypt.Crypto.Hax (LinkedFn)
open _root_.Hax (Value)

/-! ## 1. Widened arrays of narrow words -/

/-- The zero extension to 64 bits of an array of words of width `w`. -/
def widenWords {w n : Nat} (r : Fin n → BitVec w) : Fin n → BitVec 64 :=
  fun i => (r i).setWidth 64

/-- **The source value of a widened array of narrow words**: at a width `w` held in 64-bit
    slots, the source value of the widened array is the source value of its words zero
    extended to 64 bits. -/
theorem denVal_transTy_wide {w n : Nat} (hw : wideW w = 64) (x : Fin n → BitVec w) :
    denVal (wideTy (.stackArr w n)) (transTy (t := .stackArr w n) x) = arrVal (widenWords x) := by
  change denVal (.stackArr (wideW w) n) (fun i => BitVec.setWidth (wideW w) (x i)) = _
  generalize wideW w = m at hw ⊢
  subst hw
  rfl

/-- **The level check of the widened program**: the narrow-word stages accept `p`, and the
    level checker accepts their result at the all-secret labels. -/
def ctWideB {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) : Bool :=
  match narrowPrep p with
  | some q => (Dialects.NFLeak.NFProg.levelCheck (jLeakModel JLeakParams.owned) q
      (allSecret _)).isSome
  | none => false

/-- The widened program of a program that passes `ctWideB` is constant time at the all-secret
    labels, at every fuel and every valuation of the widened context. -/
theorem nfct_of_ctWideB {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (h : ctWideB p = true) {q : NFProg jasminDialect (Γ.map wideTy) ([t].map wideTy)}
    (hq : narrowPrep p = some q) (fuel : Nat) :
    NFCT (jLeakModel JLeakParams.owned) (allSecret _) fuel q := by
  unfold ctWideB at h
  rw [hq] at h
  exact Dialects.NFLeak.NFProg.nfCT_of_levelCheck _ fuel q _ h

/-! ## 2. The layout and narrow meaning of a kernel -/

/-- **The layout and narrow meaning of a kernel**: the symbol `name` and the typed parameters
    `params`; the context `Γ` of registers and stack arrays of the program, of narrow or
    64-bit words; the width `w` of the result words, held in 64-bit slots, and their number
    `nOut`; the layout `layout` returning the result in the `nOut` slots at the register
    `outReg`; the clobbered registers, the frame size of the code and its store policy, whose
    out windows lie in the result words; the reference function `ref` on the source values of
    the parameters, with results of width `w`; and the facts about the layout that `decide`
    checks. -/
structure NarrowLayoutData where
  /-- The symbol. -/
  name : String
  /-- The typed parameters. -/
  params : List (String × NFDialect.NfTy)
  /-- The context of the program. -/
  Γ : Ctxt jasminDialect
  /-- The width of the result words. -/
  w : Nat
  /-- The result words are held in 64-bit slots. -/
  hw : wideW w = 64
  /-- The number of the result words. -/
  nOut : Nat
  /-- The layout. -/
  layout : AbiLayout
  /-- The registers the code may change. -/
  clob : List String
  /-- The frame size of the code. -/
  frame : Nat
  /-- The store policy of the code. -/
  pol : StorePol
  /-- The register of the result words. -/
  outReg : String
  /-- The reference function on the source values of the parameters. -/
  ref : List Value → Option (Fin nOut → BitVec w)
  /-- The widened context holds registers and stack arrays only. -/
  regArr : regArrCtxB (Γ.map wideTy) = true
  /-- The reference function returns values only on arguments of the kinds of the layout. -/
  ref_kinds : ∀ vals r, ref vals = some r → vals.map valKind = layout.args.map (·.kind)
  /-- The kinds of the parameter types are the kinds of the layout. -/
  kinds_eq : params.map (fun p => kindOfTy (VIR.CryptoToJasminCom.mapTy
    (CatCrypt.Crypto.Hax.NFToCat.catTy p.2))) = layout.args.map (·.kind)
  /-- As many parameters as arguments of the layout. -/
  arity : params.length = layout.args.length
  /-- The argument registers are distinct. -/
  args_nodup : (layout.args.map (·.reg)).Nodup
  /-- No public array. -/
  pubWords : layout.pubWords = []
  /-- The result is the `nOut` words at `outReg`. -/
  result : layout.result = .words outReg nOut
  /-- No bound. -/
  bounds : layout.bounds = []
  /-- The regions are distinct. -/
  regions_nodup : layout.regions.Nodup
  /-- At most one region other than the result region. -/
  regions_ro : (layout.regions.filter fun p => !isResRegion layout p).length ≤ 1
  /-- The stack words lie below the return word. -/
  frameHi : layout.frameHi ≤ -8
  /-- The result words form a region of the layout. -/
  out_region : (outReg, nOut) ∈ layout.regions
  /-- The result words fit in the address space. -/
  out_fit : 8 * nOut ≤ 2 ^ 64
  /-- The out windows of the store policy lie in the result words. -/
  wins : ∀ w ∈ pol.wins, w.1 = outReg ∧ 0 ≤ w.2.1 ∧ w.2.2 ≤ 8 * nOut
  /-- The registers the read-back of the result reads at entry are registers of the layout. -/
  result_regs : ∀ r ∈ resultRegs layout.result, r ∈ abiRegs layout
  /-- The frame of the record and the return word fit below `2 ^ 64`. -/
  frame_fit : max (frame + pol.red) (-layout.frameLo).toNat + 8 ≤ 2 ^ 64

namespace NarrowLayoutData

variable (d : NarrowLayoutData)

/-- **The meaning of the kernel**: the source value of the result words of the reference
    function, zero extended to 64 bits. -/
def sem (vals : List Value) : Option Value := (d.ref vals).map fun r => arrVal (widenWords r)

/-- The results of the meaning decode as arrays of `nOut` words. -/
theorem sem_res : ∀ vals v, d.sem vals = some v →
    (dec (.arr d.nOut (.word 64)) v).isSome = true := by
  intro vals v h
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact dec_arrVal _

variable {d}

/-- The footprint of the store policy at the entry register file `ρ`: the frame and the red
    zone below the stack register, or the result words at `outReg`. -/
theorem foot {ρ : String → BitVec 64} {x : BitVec 64} (hx : KeepFoot d.pol d.frame ρ x) :
    InFrame (ρ "%rsp") (d.frame + d.pol.red) x ∨
      ∃ j < d.nOut, Ascent.AddrMem.InRange8 (X86Backend.ImageAddrSim.cellAt (ρ d.outReg) j) x := by
  rcases hx with hf | ⟨w, hw, hin⟩
  · exact Or.inl hf
  · obtain ⟨h1, h2, h3⟩ := d.wins w hw
    rw [h1] at hin
    have hm := inWin_wordsLocs h2 h3 d.out_fit hin
    obtain ⟨y, ⟨k, hk, rfl⟩, hy⟩ := Set.mem_iUnion₂.1 hm
    obtain ⟨z, hz, he⟩ := hy
    cases he
    exact Or.inr ⟨k, hk, hz⟩

end NarrowLayoutData

/-! ## 3. The data of a narrow-width region kernel -/

/-- **The data of a narrow-width region kernel**: the layout and narrow meaning of the kernel,
    and the structured program `prog` over the context `Γ` returning an array of `nOut` words
    of width `w`. Where the reference function returns `r` at the layout reading of an entry
    state, that reading is the widening `mapVal V` of a valuation `V` of `Γ`, at which the
    program denotes at some fuel, and every value it denotes is `r`. -/
structure NarrowProgKernelData extends NarrowLayoutData where
  /-- The structured program, the input of `compileRegion`. -/
  prog : NFProg jasminDialect Γ [.stackArr w nOut]
  /-- At the layout reading of an entry state where the reference function returns `r`, the
      layout reads the widening of a valuation at which the program denotes `r`. -/
  ref_read : ∀ sa r, ref (layout.args.map (·.read sa)) = some r →
    ∃ V : Ctxt.Valuation Γ, AbiValOf layout sa (mapVal V) ∧
      (∃ fuel v, prog.denote fuel V = some v) ∧
      ∀ fuel v, prog.denote fuel V = some v → v = .cons r .nil

namespace NarrowProgKernelData

variable (d : NarrowProgKernelData)

/-- The result of `compileRegion` on the program under its layout. -/
def compile : Option (JasminLprogExport.Lprog × List (BitVec 8)) :=
  compileRegion d.layout (nfAbiNames d.name d.layout) d.prog

/-- The read-only check `regionROB` of the widened program, `false` when the narrow-word stages
    refuse the program. -/
def roB : Bool :=
  match narrowPrep d.prog with
  | some q => regionROB d.layout (nfAbiNames d.name d.layout) q
  | none => false

/-- **The check of the compiled program**: the compile succeeds, the layout with the frame and
    the store policy of the data passes the footprint check `layoutFootRoB`, the widened
    program passes the read-only check `regionROB` and the level check `ctWideB`, and the
    decoded block of the bytes passes the clobber check `clobOkB` at the clobber set of the
    data. -/
def check : Bool :=
  match d.compile with
  | some (_, bytes) =>
      layoutFootRoB d.layout d.frame d.pol && d.roB && ctWideB d.prog
        && (decodeLprog bytes).all fun q => clobOkB q fun x => d.clob.contains x
  | none => false

variable {d}

/-- The compile of a checked program succeeds. -/
theorem compile_isSome (h : d.check = true) : d.compile.isSome = true := by
  unfold check at h
  cases hc : d.compile <;> simp_all

/-- The printed program and the bytes of the compiled program. -/
def compiled (h : d.check = true) : JasminLprogExport.Lprog × List (BitVec 8) :=
  d.compile.get (compile_isSome h)

/-- **The bytes of the compiled program.** -/
def bytes (h : d.check = true) : List (BitVec 8) := (compiled h).2

/-- `compileRegion` on the program returns its bytes. -/
theorem compile_eq (h : d.check = true) : d.compile = some ((compiled h).1, bytes h) := by
  rw [bytes, Prod.mk.eta]
  exact (Option.some_get (compile_isSome h)).symm

/-- The narrow-word stages accept a checked program. -/
theorem narrowPrep_isSome (h : d.check = true) : (narrowPrep d.prog).isSome = true := by
  obtain ⟨-, q, hq, -⟩ := compileRegion_eq_some.mp (compile_eq h)
  rw [hq]
  rfl

/-- **The widened program**: the result of the narrow-word stages on a checked program, the
    program the stages `regionBack` of `compileRegion` compile. -/
def wideProg (h : d.check = true) :
    NFProg jasminDialect (d.Γ.map wideTy) [wideTy (.stackArr d.w d.nOut)] :=
  (narrowPrep d.prog).get (narrowPrep_isSome h)

/-- The narrow-word stages return the widened program. -/
theorem narrowPrep_eq (h : d.check = true) : narrowPrep d.prog = some (wideProg h) :=
  (Option.some_get (narrowPrep_isSome h)).symm

/-- The four conjuncts of the check of a checked program at its bytes. -/
theorem check_parts (h : d.check = true) : layoutFootRoB d.layout d.frame d.pol = true ∧
    regionROB d.layout (nfAbiNames d.name d.layout) (wideProg h) = true ∧
    ctWideB d.prog = true ∧
    ((decodeLprog (bytes h)).all fun q => clobOkB q fun x => d.clob.contains x) = true := by
  have hc := h
  unfold check at hc
  rw [compile_eq h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨h1, ?_, h3, h4⟩
  unfold roB at h2
  rw [narrowPrep_eq h] at h2
  exact h2

/-- The bytes of a checked program decode. -/
theorem decode_isSome (h : d.check = true) : (decodeLprog (bytes h)).isSome = true :=
  decode_isSome_of_compileRegion (compile_eq h)

/-- **The decoded block of the compiled program.** -/
def block (h : d.check = true) : List RInstr := (decodeLprog (bytes h)).get (decode_isSome h)

/-- The bytes of a checked program decode to its block. -/
theorem decode_eq (h : d.check = true) : decodeLprog (bytes h) = some (block h) :=
  (Option.some_get (decode_isSome h)).symm

/-- **The clobber check of the compiled program.** -/
theorem clobOk (h : d.check = true) : clobOkB (block h) (fun x => d.clob.contains x) = true := by
  have hc := (check_parts h).2.2.2
  rw [decode_eq h, Option.all_some] at hc
  exact hc

/-- `regionBack` on the widened program returns the compiled program. -/
theorem regionBack_eq (h : d.check = true) :
    regionBack d.layout (nfAbiNames d.name d.layout) (wideProg h) =
      some ((compiled h).1, bytes h) := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_eq_some.mp (compile_eq h)
  rw [narrowPrep_eq h, Option.some.injEq] at hq
  subst hq
  exact hb

/-- The widened program of a checked program is constant time at the all-secret labels. -/
theorem nfct (h : d.check = true) (fuel : Nat) :
    NFCT (jLeakModel JLeakParams.owned) (allSecret _) fuel (wideProg h) :=
  nfct_of_ctWideB (check_parts h).2.2.1 (narrowPrep_eq h) fuel

/-- **The value-level contract of the kernel**: at an entry state where the meaning is defined,
    the layout reads back the zero-extended result words of the reference function. -/
theorem post_sem (h : d.check = true) : ∀ sa sa' v, regionPre d.layout (wideProg h) sa →
    regionPost d.layout (wideProg h) sa sa' →
    d.sem (d.layout.args.map (·.read sa)) = some v → d.layout.ResultOf sa sa' v := by
  intro sa sa' v _ ⟨V, fuel, w', hV, hw', hR⟩ hs
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨Vn, hVn, -, hden⟩ := d.ref_read sa r hr
  rw [abiValOf_unique d.regArr hV hVn, VIR.NarrowWords.narrowPrep_denote_eq (narrowPrep_eq h)]
    at hw'
  obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hw'
  obtain rfl := hden fuel v' hv'
  rw [← denVal_transTy_wide d.hw r]
  exact hR

variable (d) in
/-- **The linked function of the kernel**: the compiled program under its layout, with the
    contract of the widened program and the meaning `sem`. -/
def kernel (h : d.check = true) : LinkedFn :=
  LinkedFn.ofRegion d.name d.params (.arr d.nOut (.word 64)) d.sem d.sem_res d.layout
    (wideProg h) d.clob d.frame (bytes h) (post_sem h) d.pubWords d.pol

/-- The entry conditions of the layout hold under the resources of every call. -/
theorem layoutRegions_of_entryAt (h : d.check = true) {a : CallVar} {s : AState}
    (he : ((d.kernel h).entryAt a).holds s) : d.layout.Regions s :=
  RegionLinkCall.regions_of_entryAt d.bounds d.regions_nodup d.regions_ro
    RegionKernel.ofRegion_frameLo d.frameHi he

/-- The precondition `regionPre` of the widened program holds at every state satisfying the
    entry conditions of the layout at whose layout reading the reference function is
    defined. -/
theorem regionPre_of_regions (h : d.check = true) {sa : AState} (hr : d.layout.Regions sa)
    (hd : (d.ref (d.layout.args.map (·.read sa))).isSome = true) :
    regionPre d.layout (wideProg h) sa := by
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨Vn, hVn, ⟨fuel, v, hv⟩, -⟩ := d.ref_read sa r hr'
  exact ⟨hr, mapVal Vn, fuel, _, hVn, VIR.NarrowWords.narrowPrep_denote (narrowPrep_eq h) hv⟩

/-- **The precondition of the kernel at its call sites**: under the resources of every call
    at argument values where the meaning is defined, the precondition `regionPre` of the
    widened program holds. -/
theorem callSite_regionPre (h : d.check = true) :
    (d.kernel h).CallSitePre fun vals => ((d.kernel h).sem vals).isSome = true := by
  intro a s he hd
  refine regionPre_of_regions h (layoutRegions_of_entryAt h he) ?_
  have hv : d.layout.args.map (·.read s) = a.vals := (holds_entryAt he).2.2.1
  rw [hv]
  change (d.sem a.vals).isSome = true at hd
  simpa only [NarrowLayoutData.sem, Option.isSome_map] using hd

/-- **The code of the narrow-width kernel meets the contract of its record.** -/
theorem meets (h : d.check = true) : (d.kernel h).Meets := by
  have hspec := calleeSpec_of_regionBack_ro (args := []) (res := none) (regionBack_eq h)
    (decode_eq h) (clobOk h) (check_parts h).2.1 (check_parts h).1 (allSecret _) (nfct h)
    (pubLabelsOK_allSecret d.layout)
  exact ofRegion_meets_of_calleeSpec (decode_eq h) hspec
    (read_entryRegs_of_sub d.result_regs)
    (fun _ _ hs => LinkedFnMeets.pre_of_callSite (callSite_regionPre h) hs)
    (ofRegion_footOut d.result d.out_region d.out_fit d.wins)

/-- The parameters of the data of the kernel are the parameters of its layout. -/
theorem ins_eq (h : d.check = true) {c : CalleeData} (hc : (d.kernel h).calleeData = some c) :
    c.ins = layoutIns d.layout := by
  obtain ⟨-, -, hargs, -, -, -, -, -, -, -, -, harr⟩ := LinkedFn.calleeData_eq hc
  unfold CalleeData.ins
  rw [hargs, harr]
  rfl

/-- **The narrow-width kernel is a linked kernel** of the out shape, with the destination the
    parameter `po` of the parameters `ins` of its layout. -/
theorem linked (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (d.kernel h) where
  res_slice := by intro t ht; cases ht
  sem_kinds := by
    intro vals v hv
    obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hv
    exact (d.ref_kinds vals r hr).trans d.kinds_eq.symm
  kinds := fun _ _ => d.kinds_eq
  arity := d.arity
  args_nodup := d.args_nodup
  frame_fit := d.frame_fit
  callSite := callSite_regionPre h
  code c hc := by
    refine ⟨.out po d.nOut ?_ rfl, meets h⟩
    rw [ins_eq h hc, hins]
    exact outLayout_ofRegion hargs hdest (hpo ▸ d.result) hgp fun _ _ hx => by
      rw [hpo]
      exact NarrowLayoutData.foot hx

/-! ### The System V convention -/

variable (d) in
/-- **The linked function of the kernel at the System V convention**: the linked function
    `kernel` at the clobber set `abiClob d.clob`, which leaves out the callee-saved registers
    that the code restores. -/
def abiKernel (h : d.check = true) : LinkedFn :=
  LinkedFn.ofRegion d.name d.params (.arr d.nOut (.word 64)) d.sem d.sem_res d.layout
    (wideProg h) (abiClob d.clob) d.frame (bytes h) (post_sem h) d.pubWords d.pol

/-- **The clobber set of the kernel at the System V convention is disjoint from the
    callee-saved registers.** -/
theorem abiKernel_clob (h : d.check = true) :
    ∀ x ∈ (d.abiKernel h).clob, x ∉ X86Backend.AsmPrinter.calleeSavedRegs :=
  fun _ hx => not_mem_calleeSavedRegs_of_mem_abiClob hx

/-- **The precondition of the kernel at its call sites** at the System V convention. -/
theorem callSite_regionPre_abi (h : d.check = true) :
    (d.abiKernel h).CallSitePre fun vals => ((d.abiKernel h).sem vals).isSome = true := by
  intro a s he hd
  refine regionPre_of_regions h (RegionLinkCall.regions_of_entryAt d.bounds d.regions_nodup
    d.regions_ro RegionKernel.ofRegion_frameLo d.frameHi he) ?_
  have hv : d.layout.args.map (·.read s) = a.vals := (holds_entryAt he).2.2.1
  rw [hv]
  change (d.sem a.vals).isSome = true at hd
  simpa only [NarrowLayoutData.sem, Option.isSome_map] using hd

/-- **The code of the narrow-width kernel meets the contract at the System V convention.** -/
theorem meets_abi (h : d.check = true) : (d.abiKernel h).Meets := by
  have hspec := calleeSpec_of_regionBack_ro_saved (args := []) (res := none)
    (clob := fun x => (abiClob d.clob).contains x) (regionBack_eq h) (decode_eq h)
    (clobOkB_mono (clobOk h) fun _ hx => contains_abiClob_or hx) (check_parts h).2.1
    (check_parts h).1 (allSecret _) (nfct h) (pubLabelsOK_allSecret d.layout)
  exact ofRegion_meets_of_calleeSpec (decode_eq h) hspec
    (read_entryRegs_of_sub d.result_regs)
    (fun _ _ hs => LinkedFnMeets.pre_of_callSite (callSite_regionPre_abi h) hs)
    (ofRegion_footOut d.result d.out_region d.out_fit d.wins)

/-- The parameters of the data of the kernel at the System V convention are the parameters
    of its layout. -/
theorem ins_eq_abi (h : d.check = true) {c : CalleeData}
    (hc : (d.abiKernel h).calleeData = some c) : c.ins = layoutIns d.layout := by
  obtain ⟨-, -, hargs, -, -, -, -, -, -, -, -, harr⟩ := LinkedFn.calleeData_eq hc
  unfold CalleeData.ins
  rw [hargs, harr]
  rfl

/-- **The narrow-width kernel at the System V convention is a linked kernel** of the out
    shape, with the destination the parameter `po` of the parameters `ins` of its layout. -/
theorem linked_abi (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (d.abiKernel h) where
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
      exact NarrowLayoutData.foot hx

end NarrowProgKernelData

/-! ## 4. The check at the frame of the code -/

/-- **The check of a narrow-width kernel at the frame of its code**: `frameCheck` and the level
    check `ctWideB` of the widened program. -/
def narrowFrameCheck (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (pol : StorePol) (clob : List String) : Bool :=
  frameCheck σ a p pol clob && ctWideB p

/-- The frame of the code of a program that passes `narrowFrameCheck` fits with its red
    zone. -/
theorem fit_of_narrowFrameCheck {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {pol : StorePol} {clob : List String}
    (h : narrowFrameCheck σ a p pol clob = true) : codeFrame σ a p + redZone + 8 ≤ 2 ^ 64 :=
  fit_of_frameCheck (Bool.and_eq_true _ _ ▸ h).1

/-- **The check of a narrow-width kernel from `narrowFrameCheck`**: a kernel at the layout
    `redLayout σ F` of the frame `F` of its code, whose program, store policy and clobber set
    pass `narrowFrameCheck`, passes `NarrowProgKernelData.check`. -/
theorem NarrowProgKernelData.check_of_frameCheck {d : NarrowProgKernelData} {σ : AbiLayout}
    (hl : d.layout = redLayout σ d.frame)
    (hF : d.frame = codeFrame σ (nfAbiNames d.name σ) d.prog)
    (h : narrowFrameCheck σ (nfAbiNames d.name σ) d.prog d.pol d.clob = true) :
    d.check = true := by
  unfold narrowFrameCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hct⟩ := h
  unfold frameCheck at h
  split at h
  · rename_i F P bs ro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcomp, q, hq, hro⟩ := frameCompile_spec hc
    have hF' : d.frame = F := by rw [hF, codeFrame, hc]; rfl
    have ha : nfAbiNames d.name d.layout = nfAbiNames d.name σ := by rw [hl]; rfl
    unfold NarrowProgKernelData.check NarrowProgKernelData.compile NarrowProgKernelData.roB
    rw [ha, hq, hl, hF', hcomp, hct]
    simp only [hro, h.1.1.2, h.1.2, h.2, Bool.and_self]
  · cases h

/-! ## 5. Narrow-width template kernels -/

/-- **The data of a narrow-width template kernel**: the layout and narrow meaning of the
    kernel, and the template `body`, a straight-line program over the context `Γ` returning an
    array of `nOut` words of width `w`. Where the reference function returns `r` at the layout
    reading of an entry state, that reading is the widening `mapVal V` of a valuation `V` of
    `Γ` at which the template has the value `r`. -/
structure NarrowTemplateKernelData extends NarrowLayoutData where
  /-- The template. -/
  body : Com jasminDialect Γ (.stackArr w nOut)
  /-- At the layout reading of an entry state where the reference function returns `r`, the
      layout reads the widening of a valuation at which the template has the value `r`. -/
  ref_read : ∀ sa r, ref (layout.args.map (·.read sa)) = some r →
    ∃ V : Ctxt.Valuation Γ, AbiValOf layout sa (mapVal V) ∧ body.denote V = r

namespace NarrowTemplateKernelData

variable (d : NarrowTemplateKernelData)

/-- The structured program of the template, the input of `compileRegion`. -/
def prog : NFProg jasminDialect d.Γ [.stackArr d.w d.nOut] := NFProg.ofCom d.body

/-- **The narrow-width region kernel of a template**: the template embedded by
    `NFProg.ofCom`. -/
def toNarrowProgKernelData : NarrowProgKernelData where
  toNarrowLayoutData := d.toNarrowLayoutData
  prog := d.prog
  ref_read sa r hr := by
    obtain ⟨V, hV, hb⟩ := d.ref_read sa r hr
    refine ⟨V, hV, ⟨0, _, NFProg.denote_ofCom _ _ _⟩, fun fuel v hv => ?_⟩
    rw [prog, NFProg.denote_ofCom, Option.some.injEq] at hv
    rw [← hv, hb]

/-- **The check of the compiled template**: `NarrowProgKernelData.check` of its region
    kernel. -/
def check : Bool := d.toNarrowProgKernelData.check

/-- **The linked function of the template kernel**. -/
def kernel (h : d.check = true) : LinkedFn := d.toNarrowProgKernelData.kernel h

/-- **The linked function of the template kernel at the System V convention**. -/
def abiKernel (h : d.check = true) : LinkedFn := d.toNarrowProgKernelData.abiKernel h

variable {d}

/-- **The code of the narrow-width template kernel meets the contract of its record.** -/
theorem meets (h : d.check = true) : (d.kernel h).Meets :=
  NarrowProgKernelData.meets h

/-- **The narrow-width template kernel is a linked kernel** of the out shape, with the
    destination the parameter `po` of the parameters `ins` of its layout. -/
theorem linked (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (d.kernel h) :=
  NarrowProgKernelData.linked h hins hargs hdest hgp hpo

/-- **The code of the narrow-width template kernel meets the contract at the System V
    convention.** -/
theorem meets_abi (h : d.check = true) : (d.abiKernel h).Meets :=
  NarrowProgKernelData.meets_abi h

/-- **The narrow-width template kernel at the System V convention is a linked kernel** of the
    out shape. -/
theorem linked_abi (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (d.abiKernel h) :=
  NarrowProgKernelData.linked_abi h hins hargs hdest hgp hpo

end NarrowTemplateKernelData

end CatCrypt.Crypto.SecureCompilation.HashTemplate
