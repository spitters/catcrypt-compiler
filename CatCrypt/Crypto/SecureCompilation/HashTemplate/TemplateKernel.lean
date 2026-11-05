/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
public import CatCrypt.Crypto.SecureCompilation.Haxc.Decompile
public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkedKernel
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakOfCom
public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem

/-!
# Template kernels: region-compiled linked kernels of the out shape

A region kernel is a structured program `NFProg` over a context of registers and stack arrays
whose result is an array of `nOut` words, with a layout that returns the result in the words at
the register `outReg`, a meaning given by a reference function on the source values of the
parameters, and the facts about the layout that `decide` checks. The structure
`ProgKernelData` collects these data; `ProgKernelData.kernel` is the linked function of
`LinkedFn.ofRegion` at the bytes of `compileRegion`, and `ProgKernelData.meets` and
`ProgKernelData.linked` give its contract and its linked-kernel structure from one decided
fact `ProgKernelData.check` (the compile succeeds, the layout passes the footprint check
`layoutFootRoB`, the program passes the read-only check `regionROB`, and the decoded block of
its bytes passes the clobber check `clobOkB`) and the parameters of its data (`layoutIns`),
through `calleeSpec_of_compileRegion_ro`. The bytes of every result of `compileRegion` decode
(`decode_isSome_of_compileRegion`), from the decodability conjunct of the printed class that
the gate `regionCoB` checks.

A template kernel (`TemplateKernelData`) is the instance at the embedding `NFProg.ofCom` of a
straight-line template `Com` with fixed events.

A kernel at the frame of its code has the layout `redLayout σ F`, whose stack words are the
frame of `F` bytes and the red zone of `redZone` bytes below it, with `F` the frame size
`codeFrame` of the compiled code. `frameCompile` runs the back half once (the gate, the
narrow-word stages and `frameBack`): the stages before
the gate do not read the stack words of the layout, so it reads `F` off the printed body and
gates that body at `redLayout σ F`, with the read-only check of `regionROB` in the same pass;
`frameCheck` decides the check of such a kernel from that one result
(`ProgKernelData.check_of_frameCheck`).

## Main definitions

* `KernelLayoutData`: the symbol, parameters, layout and meaning of a kernel.
* `ProgKernelData`: the data of a region kernel over a structured program.
* `ProgKernelData.check`: the compile, footprint, read-only and clobber check, as one Boolean.
* `ProgKernelData.kernel`: the linked function of the compiled program.
* `TemplateKernelData`: the data of a template kernel, and `TemplateKernelData.toProgKernelData`.
* `layoutIns`: the parameters the region back half reads off a layout.
* `redZone`, `redLayout`, `frameBack`, `frameCompile`, `codeFrame`, `frameCheck`: the layout
  at the frame of the code, the stages `regionBack` and the back half at it, and the check at
  it.
* `ProgKernelData.backProg`: the program the stages `regionBack` compile, the widened program
  carried back to the context of the kernel.

## Main statements

* `decode_isSome_of_compileRegion`: the bytes of every result of `compileRegion` decode.
* `ProgKernelData.post_sem`: the value-level contract of the kernel.
* `ProgKernelData.callSite_regionPre`: the precondition of the kernel holds at its call sites.
* `ProgKernelData.meets`: the code of the kernel meets the contract of its record.
* `ProgKernelData.linked`: the kernel is a linked kernel of the out shape.
* `TemplateKernelData.meets`, `TemplateKernelData.linked`: the same for a template kernel.
* `frameCompile_spec`: a result of `frameCompile` is the result of `compileRegion` and of
  `regionROB` on the widened program at the layout of its frame.
* `ProgKernelData.backProg_denote`: the program `regionBack` compiles denotes what the program
  denotes, so the interface of the callee is that of the program
  (`RegionKernel.regionSig_congr`).
* `fit_of_frameCheck`, `ProgKernelData.check_of_frameCheck`: the frame fits and the kernel
  passes its check when `frameCheck` holds.
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
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels lvlOf)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT allSecret)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf abiValOf_unique)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (regArrCtxB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (CallVar isResRegion
  holds_entryAt)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem (clobOkB layoutFootRoB
  calleeSpec_of_regionBack_ro)
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (narrowPrep castProg wideTy)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep (regionROB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (frameSize)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys gpOk)
open CatCrypt.Crypto.Hax (LinkedFn)
open _root_.Hax (Value)

/-! ## 1. Source values of words and word arrays -/

/-- The source value of a word array decodes as an array of words. -/
theorem dec_arrVal {n : Nat} (a : Fin n → BitVec 64) :
    (dec (.arr n (.word 64)) (arrVal a)).isSome = true := by
  obtain ⟨f, hf, -⟩ := CatCrypt.Crypto.Hax.ImpToNF.dec_arr_word (n := n)
    ((List.range n).map fun j => Value.int (stackGet a j).toNat)
    (fun v hv => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, rfl, (stackGet a j).isLt⟩)
    (by simp)
  rw [arrVal, hf]
  rfl

/-- A value that decodes as a word is a scalar. -/
theorem valKind_of_dec_word {v : Value} {x : BitVec 64} (h : dec (.word 64) v = some x) :
    valKind v = .scalar := by
  cases v <;> first | rfl | cases h

/-- A value that decodes as an array of `n` words is an array of `n` words. -/
theorem valKind_of_dec_arr {n : Nat} {v : Value} {x : Fin n → BitVec 64}
    (h : dec (.arr n (.word 64)) v = some x) : valKind v = .words n := by
  obtain ⟨vs, rfl, hl⟩ := dec_arr_eq_some h
  rw [← hl]
  rfl

/-- The all-secret labels agree with the public data of every layout. -/
theorem pubLabelsOK_allSecret (σ : AbiLayout) {Γ : Ctxt jasminDialect} :
    PubLabelsOK σ (allSecret Γ) := by
  intro t v hv
  exfalso
  induction v with
  | here => cases hv
  | there v ih => exact ih hv

/-- **The parameters of the data of a layout**: each argument register in the upper-case
    names of the region back half, with the kind of its argument, as `CalleeData.ins` reads
    them off the data of a linked function with the layout `σ`. -/
def layoutIns (σ : AbiLayout) : List (String × ArgKind) :=
  (σ.args.map fun a => ((a.reg.drop 1).toString).toUpper).mapIdx fun i a =>
    (a, match CatCrypt.Crypto.Hax.insArrArgs (σ.args.map (·.kind)) i with
      | some m => .words m
      | none => .scalar)

/-! ## 2. The layout and meaning of a kernel -/

/-- **The layout and meaning of a kernel**: the symbol `name` and the typed parameters
    `params`; the context `Γ` of registers and stack arrays of the program and the number
    `nOut` of its result words; the layout `layout` returning the result in the `nOut` words
    at the register `outReg`; the clobbered registers, the frame size of the code and its
    store policy, whose out windows lie in the result words; the reference function `ref` on
    the source values of the parameters; the valuation `val` the layout reads off an entry
    state; and the facts about the layout that `decide` checks. -/
structure KernelLayoutData where
  /-- The symbol. -/
  name : String
  /-- The typed parameters. -/
  params : List (String × NFDialect.NfTy)
  /-- The context of the program. -/
  Γ : Ctxt jasminDialect
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
  ref : List Value → Option (Fin nOut → BitVec 64)
  /-- The valuation the layout reads off an entry state. -/
  val : AState → Ctxt.Valuation Γ
  /-- The layout reads `val sa` off the entry state `sa`. -/
  abiValOf_val : ∀ sa, AbiValOf layout sa (val sa)
  /-- The context holds registers and stack arrays only. -/
  regArr : regArrCtxB Γ = true
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

/-! ## 3. The bytes of the region back half decode -/

section Decode

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (shapesD shapesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (printedAddrB bodyFacts_of shapesOf_spec expectedFrom_fundef targetsOK_of)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (printedAddrWB bodyFactsW_of targetsOK_ofW)

/-- The bytes of a body of the printed class `printedAddrB` decode. -/
theorem decode_isSome_of_printedAddrB {body : JasminLprogExport.Lcmd}
    (h : printedAddrB body = true) : (decodeLprog (encodeLfundefBytes body)).isSome = true := by
  obtain ⟨shs, hF⟩ := bodyFacts_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrB, Bool.and_eq_true] at h
    exact h.1.1.1
  obtain ⟨hl, -⟩ := shapesOf_spec _ body shs hF.shapes
  rw [decodeLprog_encodeLfundefBytes hdec (by
    rw [fundefLayout, fundefItems,
      show shapesD (Params.ofBody body) body = shs by
        rw [shapesD, show shapesOf (Params.ofBody body) body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_of hF))]
  rfl

/-- The bytes of a body of the printed class `printedAddrWB` decode. -/
theorem decode_isSome_of_printedAddrWB {body : JasminLprogExport.Lcmd}
    (h : printedAddrWB body = true) : (decodeLprog (encodeLfundefBytes body)).isSome = true := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrWB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1
  obtain ⟨hl, -⟩ := shapesOf_spec _ body shs hF.shapes
  rw [decodeLprog_encodeLfundefBytes hdec (by
    rw [fundefLayout, fundefItems,
      show shapesD (Params.ofBody body) body = shs by
        rw [shapesD, show shapesOf (Params.ofBody body) body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_ofW hF))]
  rfl

/-- The bytes of a body that passes the gate of the image simulation decode. -/
theorem decode_isSome_of_regionImgB {sl : String → Option (String × Nat)}
    {R : List (String × Nat)}
    {outs : List String} {body : JasminLprogExport.Lcmd} (h : regionImgB sl R outs body = true) :
    (decodeLprog (encodeLfundefBytes body)).isSome = true := by
  have hc := regionImgCoreB_of_regionImgB h
  simp only [regionImgCoreB, Bool.and_eq_true] at hc
  exact decode_isSome_of_printedAddrWB hc.1.1.1.1

/-- **The bytes of the region back half decode**: every result of `compileRegion` has bytes
    that `decodeLprog` decodes. -/
theorem decode_isSome_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes)) :
    (decodeLprog bytes).isSome = true := by
  obtain ⟨-, -, -, -, -, r, b, cert, -, -, hb, hco, -⟩ := compileRegion_spec h
  simp only [regionCoB, Bool.and_eq_true] at hco
  have hi := hco.2.2
  simp only [renImageB, calleeImgBT_none, Bool.and_eq_true] at hi
  rw [encodeLfundefBytesChecked_eq hb]
  exact decode_isSome_of_regionImgB hi.1.1.1.1.2

end Decode

/-! ## 4. The data of a region kernel over a structured program -/

/-- **The data of a region kernel**: the layout and meaning of the kernel, and the structured
    program `prog` over the context `Γ` returning an array of `nOut` words, constant time at
    the all-secret labels; at the layout reading of an entry state where the reference
    function is defined, the program denotes, and every value it denotes is the value of the
    reference function. -/
structure ProgKernelData extends KernelLayoutData where
  /-- The structured program, the input of `compileRegion`. -/
  prog : NFProg jasminDialect Γ [.stackArr 64 nOut]
  /-- Where the reference function returns `r` at the layout reading of an entry state, every
      value the program denotes at the valuation of that state is `r`. -/
  ref_read : ∀ sa r fuel v, ref (layout.args.map (·.read sa)) = some r →
    prog.denote fuel (val sa) = some v → v = .cons r .nil
  /-- Where the reference function is defined at the layout reading of an entry state
      satisfying the entry conditions, the program denotes at some fuel. -/
  denotes : ∀ sa, layout.Regions sa → (ref (layout.args.map (·.read sa))).isSome = true →
    ∃ fuel v, prog.denote fuel (val sa) = some v
  /-- The program is constant time at the all-secret labels. -/
  nfct : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) (allSecret Γ) fuel prog

/-- **The context of a kernel holds 64-bit words**: the layout reads a valuation of it off an
    entry state (`map_wideTy_of_abiValOf`), so the widening fixes it. -/
theorem KernelLayoutData.wide (d : KernelLayoutData) : d.Γ.map wideTy = d.Γ :=
  map_wideTy_of_abiValOf _ (d.abiValOf_val { regs := fun _ => 0, mem := fun _ => 0 })

/-- The result type of a kernel, an array of 64-bit words, is fixed by the widening. -/
theorem wideTy_words (n : Nat) : [JasminTy.stackArr 64 n].map wideTy = [.stackArr 64 n] := rfl

/-- A program carried along equalities of its context and result type is checked by
    `regionROB` as the program. -/
theorem regionROB_castProg (σ : AbiLayout) (a : AbiNames) {Γ Γ' : Ctxt jasminDialect}
    {t t' : JasminTy} (e₁ : Γ' = Γ) (e₂ : [t'] = [t]) (r : NFProg jasminDialect Γ' [t']) :
    regionROB σ a (castProg e₁ e₂ r) = regionROB σ a r := by
  subst e₁
  obtain rfl : t' = t := (List.cons.inj e₂).1
  rfl

namespace ProgKernelData

variable (d : ProgKernelData)

/-- **The program the stages `regionBack` compile**: the result of the narrow-word stages on the
    program, carried back to its context and result type (`castProg`), which the widening
    fixes; the program itself where the stages refuse it. -/
def backProg : NFProg jasminDialect d.Γ [.stackArr 64 d.nOut] :=
  match narrowPrep d.prog with
  | some q => castProg d.wide (wideTy_words d.nOut) q
  | none => d.prog

/-- Unfolding lemma of `backProg` at a result of the narrow-word stages. -/
theorem backProg_eq {q} (hq : narrowPrep d.prog = some q) :
    d.backProg = castProg d.wide (wideTy_words d.nOut) q := by
  unfold backProg
  rw [hq]

/-- The program `regionBack` compiles denotes what the program denotes. -/
theorem backProg_denote {q} (hq : narrowPrep d.prog = some q) (fuel : Nat)
    (V : Ctxt.Valuation d.Γ) : d.backProg.denote fuel V = d.prog.denote fuel V := by
  rw [d.backProg_eq hq]
  exact VIR.NarrowWords.narrowPrep_cast_denote d.wide (wideTy_words d.nOut) hq fuel V

/-- **The meaning of the kernel**: the source value of the array of the reference function. -/
def sem (vals : List Value) : Option Value := (d.ref vals).map arrVal

/-- The results of the meaning decode as arrays of `nOut` words. -/
theorem sem_res : ∀ vals v, d.sem vals = some v →
    (dec (.arr d.nOut (.word 64)) v).isSome = true := by
  intro vals v h
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact dec_arrVal r

/-- The result of `compileRegion` on the program under its layout. -/
def compile : Option (JasminLprogExport.Lprog × List (BitVec 8)) :=
  compileRegion d.layout (nfAbiNames d.name d.layout) d.prog

/-- **The check of the compiled program**: the compile succeeds, the layout with the frame
    and the store policy of the data passes the footprint check `layoutFootRoB`, the program
    `backProg` passes the read-only check `regionROB`, and the decoded block of the bytes passes the
    clobber check `clobOkB` at the clobber set of the data. The bytes of every result of
    `compileRegion` decode (`decode_isSome_of_compileRegion`). The read-only check is taken on
    the program `backProg` that the stages `regionBack` compile. -/
def check : Bool :=
  match d.compile with
  | some (_, bytes) =>
      layoutFootRoB d.layout d.frame d.pol
        && regionROB d.layout (nfAbiNames d.name d.layout) d.backProg
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

/-- The three conjuncts of the check of a checked program at its bytes. -/
theorem check_parts (h : d.check = true) : layoutFootRoB d.layout d.frame d.pol = true ∧
    regionROB d.layout (nfAbiNames d.name d.layout) d.backProg = true ∧
    ((decodeLprog (bytes h)).all fun q => clobOkB q fun x => d.clob.contains x) = true := by
  have hc := h
  unfold check at hc
  rw [compile_eq h] at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

/-- The layout of a checked program passes the footprint check. -/
theorem footRo (h : d.check = true) : layoutFootRoB d.layout d.frame d.pol = true :=
  (check_parts h).1

/-- A checked program passes the read-only check. -/
theorem regionRO (h : d.check = true) :
    regionROB d.layout (nfAbiNames d.name d.layout) d.backProg = true :=
  (check_parts h).2.1

/-- The bytes of a checked program decode to a block that passes the clobber check. -/
theorem decode_clob (h : d.check = true) : ∃ q, decodeLprog (bytes h) = some q ∧
    clobOkB q (fun x => d.clob.contains x) = true := by
  have hc := (check_parts h).2.2
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (decode_isSome_of_compileRegion (compile_eq h))
  simp only [hq, Option.all_some] at hc
  exact ⟨q, hq, hc⟩

/-- The bytes of a checked program decode. -/
theorem decode_isSome (h : d.check = true) : (decodeLprog (bytes h)).isSome = true := by
  obtain ⟨q, hq, -⟩ := decode_clob h
  rw [hq]
  rfl

/-- **The decoded block of the compiled program.** -/
def block (h : d.check = true) : List RInstr := (decodeLprog (bytes h)).get (decode_isSome h)

/-- The bytes of a checked program decode to its block. -/
theorem decode_eq (h : d.check = true) : decodeLprog (bytes h) = some (block h) :=
  (Option.some_get (decode_isSome h)).symm

/-- **The clobber check of the compiled program.** -/
theorem clobOk (h : d.check = true) : clobOkB (block h) (fun x => d.clob.contains x) = true := by
  obtain ⟨q, hq, hk⟩ := decode_clob h
  rw [decode_eq h, Option.some.injEq] at hq
  rw [hq]
  exact hk

variable (d)

/-- **The value-level contract of the kernel.** -/
theorem post_sem : ∀ sa sa' v, regionPre d.layout d.prog sa →
    regionPost d.layout d.prog sa sa' →
    d.sem (d.layout.args.map (·.read sa)) = some v → d.layout.ResultOf sa sa' v := by
  intro sa sa' v _ ⟨V, fuel, w', hV, hw', hR⟩ hs
  rw [abiValOf_unique d.regArr hV (d.abiValOf_val sa)] at hw'
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain rfl := d.ref_read sa r fuel w' hr hw'
  exact hR

/-- **The linked function of the kernel**: the compiled program under its layout, with the
    meaning `sem`. -/
def kernel (h : d.check = true) : LinkedFn :=
  LinkedFn.ofRegion d.name d.params (.arr d.nOut (.word 64)) d.sem d.sem_res d.layout d.prog
    d.clob d.frame (bytes h) d.post_sem d.pubWords d.pol

/-- The precondition of the region-compiled program holds at every state satisfying the
    entry conditions of the layout at whose layout reading the reference function is
    defined. -/
theorem regionPre_of_regions {sa : AState} (h : d.layout.Regions sa)
    (hr : (d.ref (d.layout.args.map (·.read sa))).isSome = true) :
    regionPre d.layout d.prog sa := by
  obtain ⟨fuel, v, hv⟩ := d.denotes sa h hr
  exact ⟨h, d.val sa, fuel, v, d.abiValOf_val sa, hv⟩

variable {d}

/-- The entry conditions of the layout hold under the resources of every call. -/
theorem layoutRegions_of_entryAt (h : d.check = true) {a : CallVar} {s : AState}
    (he : ((kernel d h).entryAt a).holds s) : d.layout.Regions s :=
  RegionLinkCall.regions_of_entryAt d.bounds d.regions_nodup d.regions_ro
    RegionKernel.ofRegion_frameLo d.frameHi he

/-- **The precondition of the kernel at its call sites**: under the resources of every call
    at argument values where the meaning is defined, the precondition `regionPre` of the
    record holds. -/
theorem callSite_regionPre (h : d.check = true) :
    (kernel d h).CallSitePre fun vals => ((kernel d h).sem vals).isSome = true := by
  intro a s he hd
  refine d.regionPre_of_regions (layoutRegions_of_entryAt h he) ?_
  have hv : d.layout.args.map (·.read s) = a.vals := (holds_entryAt he).2.2.1
  rw [hv]
  change (d.sem a.vals).isSome = true at hd
  simpa only [sem, Option.isSome_map] using hd

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

/-- **The code of the kernel meets the contract of its record.** -/
theorem meets (h : d.check = true) : (kernel d h).Meets := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_wide d.wide (wideTy_words d.nOut) (compile_eq h)
  rw [← d.backProg_eq hq] at hb
  have hspec := calleeSpec_of_regionBack_ro (args := []) (res := none) hb (decode_eq h)
    (clobOk h) (regionRO h) (footRo h) (allSecret d.Γ)
    (fun fuel => d.backProg_eq hq ▸ VIR.NarrowWords.narrowPrep_cast_nfct (fun _ => rfl) d.wide
      (wideTy_words d.nOut) hq (d.nfct fuel))
    (pubLabelsOK_allSecret d.layout)
  rw [regionSig_congr d.layout (d.backProg_denote hq)] at hspec
  exact ofRegion_meets_of_calleeSpec (decode_eq h) hspec
    (read_entryRegs_of_sub d.result_regs)
    (fun _ _ hs => LinkedFnMeets.pre_of_callSite (callSite_regionPre h) hs)
    (ofRegion_footOut d.result d.out_region d.out_fit d.wins)

/-- The parameters of the data of the kernel are the parameters of its layout. -/
theorem ins_eq (h : d.check = true) {c : CalleeData} (hc : (kernel d h).calleeData = some c) :
    c.ins = layoutIns d.layout := by
  obtain ⟨-, -, hargs, -, -, -, -, -, -, -, -, harr⟩ := LinkedFn.calleeData_eq hc
  unfold CalleeData.ins
  rw [hargs, harr]
  rfl

/-- **The kernel is a linked kernel** of the out shape, with the destination the parameter
    `po` of the parameters `ins` of its layout. -/
theorem linked (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (kernel d h) where
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
      exact foot hx

end ProgKernelData

/-! ## 5. Template kernels -/

/-- **The data of a template kernel**: the layout and meaning of the kernel, and the template
    `body`, a straight-line program over the context `Γ` returning an array of `nOut` words,
    with fixed events, at whose value the reference function returns at the layout reading
    of every entry state. -/
structure TemplateKernelData extends KernelLayoutData where
  /-- The template. -/
  body : Com jasminDialect Γ (.stackArr 64 nOut)
  /-- The events of the template are fixed. -/
  events : LeakFixed (jLeakModel JLeakParams.owned) body
  /-- At the layout reading of an entry state, the reference function returns the value of
      the template. -/
  ref_read : ∀ sa, ref (layout.args.map (·.read sa)) = some (body.denote (val sa))

namespace TemplateKernelData

variable (d : TemplateKernelData)

/-- The structured program of the template, the input of `compileRegion`. -/
def prog : NFProg jasminDialect d.Γ [.stackArr 64 d.nOut] := NFProg.ofCom d.body

/-- **The region kernel of a template**: the template embedded by `NFProg.ofCom`. -/
def toProgKernelData : ProgKernelData where
  toKernelLayoutData := d.toKernelLayoutData
  prog := d.prog
  ref_read sa r fuel v hr hv := by
    rw [prog, NFProg.denote_ofCom, Option.some.injEq] at hv
    rw [d.ref_read sa, Option.some.injEq] at hr
    rw [← hv, hr]
  denotes sa _ _ := ⟨0, _, NFProg.denote_ofCom _ _ _⟩
  nfct := Dialects.NFLeak.nfct_ofCom_of_fixed _ _ d.events (allSecret d.Γ)

/-- **The meaning of the kernel**: the source value of the array of the reference function. -/
def sem (vals : List Value) : Option Value := d.toProgKernelData.sem vals

/-- **The check of the compiled template**: `ProgKernelData.check` of its region kernel. -/
def check : Bool := d.toProgKernelData.check

/-- **The linked function of the template kernel**: the compiled template under its layout,
    with the meaning `sem`. -/
def kernel (h : d.check = true) : LinkedFn := d.toProgKernelData.kernel h

/-- **The value-level contract of the kernel.** -/
theorem post_sem : ∀ sa sa' v, regionPre d.layout d.prog sa →
    regionPost d.layout d.prog sa sa' →
    d.sem (d.layout.args.map (·.read sa)) = some v → d.layout.ResultOf sa sa' v :=
  d.toProgKernelData.post_sem

/-- The precondition of the region-compiled template holds at every state satisfying the
    entry conditions of the layout: the template denotes at every valuation. -/
theorem regionPre_of_regions {sa : AState} (h : d.layout.Regions sa) :
    regionPre d.layout d.prog sa :=
  ⟨h, d.val sa, 0, _, d.abiValOf_val sa, NFProg.denote_ofCom _ _ _⟩

variable {d}

/-- **The precondition of the kernel at its call sites**: under the resources of every call
    the precondition `regionPre` of the record holds. -/
theorem callSite_regionPre (h : d.check = true) :
    (kernel d h).CallSitePre fun vals => ((kernel d h).sem vals).isSome = true :=
  ProgKernelData.callSite_regionPre h

/-- **The code of the template kernel meets the contract of its record.** -/
theorem meets (h : d.check = true) : (kernel d h).Meets :=
  ProgKernelData.meets h

/-- **The template kernel is a linked kernel** of the out shape, with the destination the
    parameter `po` of the parameters `ins` of its layout. -/
theorem linked (h : d.check = true) {ins : List (String × ArgKind)} {po : String}
    (hins : layoutIns d.layout = ins)
    (hargs : d.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words d.nOut) ∈ ins) (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hpo : phys po = d.outReg) : LinkedKernel (kernel d h) :=
  ProgKernelData.linked h hins hargs hdest hgp hpo

end TemplateKernelData

/-! ## 6. Kernels at the frame of their code -/

/-- The size in bytes of the red zone below the frame of the code of a kernel. -/
def redZone : Nat := 128

/-- **The layout at a frame size**: the layout `σ` with the stack words from `F + redZone`
    bytes below the entry stack pointer, the frame of `F` bytes of the code and the red zone
    below it. -/
def redLayout (σ : AbiLayout) (F : Nat) : AbiLayout :=
  { σ with frameLo := -((F + redZone : Nat) : Int) }

/-- Unfolding lemma of `redLayout`: the parameters of `redLayout σ F` are those of `σ`. -/
theorem redLayout_args (σ : AbiLayout) (F : Nat) : (redLayout σ F).args = σ.args := rfl

/-- Unfolding lemma of `redLayout`: the parameters the region back half reads off
    `redLayout σ F` are those of `σ`. -/
theorem layoutIns_redLayout (σ : AbiLayout) (F : Nat) :
    layoutIns (redLayout σ F) = layoutIns σ := rfl

/-- The layout reading of an entry state at `σ` is its layout reading at `redLayout σ F`. -/
theorem abiValOf_redLayout {σ : AbiLayout} {F : Nat} {sa : AState} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} (h : AbiValOf σ sa V) : AbiValOf (redLayout σ F) sa V :=
  ⟨h.arg, h.reg, h.arr⟩

/-- The frame of `F` bytes with the red zone, and the stack words of `redLayout σ F`, fit with
    the return word below `2 ^ 64`. -/
theorem redLayout_frame_fit {σ : AbiLayout} {F : Nat} {wins : List (String × Int × Int)}
    (h : F + redZone + 8 ≤ 2 ^ 64) :
    max (F + (⟨redZone, wins⟩ : StorePol).red) (-(redLayout σ F).frameLo).toNat + 8 ≤ 2 ^ 64 := by
  change max (F + redZone) (-(-((F + redZone : Nat) : Int))).toNat + 8 ≤ 2 ^ 64
  rw [Int.neg_neg, Int.toNat_natCast, Nat.max_self]
  exact h

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (exportR regionExportableB) in
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep (roKeepB) in
/-- **The stages `regionBack` at the frame of the code**, in one pass: the stages of
    `regionBack` without linked functions, the webs of the export among them, up to the first body `b` of
    the printed program, whose stages do
    not read the stack words of the layout; then, at the layout `redLayout σ (frameSize b)`,
    the gated encoder, the gate of `regionBack` and the read-only check `roKeepB` of
    `regionROB`. The frame size, the printed program, the bytes and the read-only flag, or
    `none` when a stage declines or the gate refuses. -/
def frameBack (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) :
    Option (Nat × JasminLprogExport.Lprog × List (BitVec 8) × Bool) :=
  if regionExportableB (legalizeRegion p) = true then
    match exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 with
    | some r0 =>
        match regionCallee [] (legalizeRegion p) r0.code with
        | some _ =>
            let r := regionWebsAt (regionWebsEx σ exportReg) none r0
            match regionLprogC a (legalizeRegion p) none (regionWebsEx σ exportReg) with
            | some (P, cert) =>
                match firstBody (printedLprog P) with
                | some b =>
                    match X86Backend.LprogBytes.encodeLfundefBytesChecked b with
                    | some bs =>
                        if regionCoB (redLayout σ (frameSize b)) exportReg b t r.code r.res cert
                              none a.fname
                            && regionCtB (redLayout σ (frameSize b)) exportReg b t r.code r.res
                              cert then
                          let q := regionCoParts (redLayout σ (frameSize b)) exportReg b t r.code
                            r.res cert
                          some (frameSize b, printedLprog P, bs,
                            roKeepB (redLayout σ (frameSize b)) exportReg q.ps q.cells
                              (q.outs ++ q.cellOuts) b q.ref)
                        else none
                    | none => none
                | none => none
            | none => none
        | none => none
    | none => none
  else none

/-- **The facts of a result of `frameBack`**: `regionBack` at the layout
    `redLayout σ F` of its frame size `F` returns its printed program and bytes, and
    `regionROB` at that layout is its read-only flag. -/
theorem frameBack_spec {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {F : Nat} {P : JasminLprogExport.Lprog}
    {bs : List (BitVec 8)} {ro : Bool} (h : frameBack σ a p = some (F, P, bs, ro)) :
    regionBack (redLayout σ F) a p = some (P, bs) ∧ regionROB (redLayout σ F) a p = ro := by
  unfold frameBack at h
  split at h
  · rename_i hB
    split at h
    · rename_i r hr
      split at h
      · rename_i c hc
        obtain rfl := regionCallee_nil hc
        split at h
        · rename_i P0 cert hP
          split at h
          · rename_i b hb
            split at h
            · rename_i bs' hbs
              dsimp only at h
              split at h
              · rename_i hg
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                have hw : regionWebsEx (redLayout σ (frameSize b)) exportReg =
                    regionWebsEx σ exportReg := rfl
                constructor
                · unfold regionBack regionEncode
                  rw [ite_eq_left hB]
                  simp only [hr, hc, hw, hP, hb, calleeBytes_none, hbs,
                    calleeCtB_none, hg, ite_true]
                · unfold regionROB
                  rw [hr, Option.map_some, hw, hP]
                  simp only [hb]
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The back half at the frame of the code**: the gate `regionExportableB` and the
    narrow-word stages of `compileRegion`, then `frameBack` on the widened program. The frame
    size, the printed program, the bytes and the read-only flag, or `none` when a stage
    declines or the gate refuses. -/
def frameCompile (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) :
    Option (Nat × JasminLprogExport.Lprog × List (BitVec 8) × Bool) :=
  if JasminLprogExport.ExportRegions.regionExportableB p = true then
    (narrowPrep p).bind (frameBack σ a)
  else none

/-- **The facts of a result of `frameCompile`**: `compileRegion` at the layout
    `redLayout σ F` of its frame size `F` returns its printed program and bytes, and
    `regionROB` at that layout of the widened program is its read-only flag. -/
theorem frameCompile_spec {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {F : Nat} {P : JasminLprogExport.Lprog}
    {bs : List (BitVec 8)} {ro : Bool} (h : frameCompile σ a p = some (F, P, bs, ro)) :
    compileRegion (redLayout σ F) a p = some (P, bs) ∧
      ∃ q, narrowPrep p = some q ∧ regionROB (redLayout σ F) a q = ro := by
  unfold frameCompile at h
  split at h
  · rename_i hB
    obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hc, hro⟩ := frameBack_spec hf
    exact ⟨compileRegion_eq_some.mpr ⟨hB, q, hq, hc⟩, q, hq, hro⟩
  · cases h

/-- **The frame size of the code** of `p` under `σ`: the frame size of the first body of the
    printed program of `frameCompile` (the size its first instruction `leaq -F(%rsp), %rsp`
    reserves), `0` when it fails. -/
def codeFrame (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : Nat :=
  ((frameCompile σ a p).map (·.1)).getD 0

/-- **The check of a region kernel at the frame of its code**, decided by one evaluation of
    `frameCompile`: the frame with the red zone fits below `2 ^ 64`, the layout
    `redLayout σ F` with the frame `F` and the store policy `pol` passes `layoutFootRoB`, the
    read-only flag holds, and the decoded block of the bytes passes `clobOkB` at `clob`. -/
def frameCheck (σ : AbiLayout) (a : AbiNames) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (pol : StorePol) (clob : List String) : Bool :=
  match frameCompile σ a p with
  | some (F, _, bs, ro) =>
      decide (F + redZone + 8 ≤ 2 ^ 64) && layoutFootRoB (redLayout σ F) F pol && ro
        && (decodeLprog bs).all fun q => clobOkB q fun x => clob.contains x
  | none => false

/-- The frame of the code of a program that passes `frameCheck` fits with its red zone. -/
theorem fit_of_frameCheck {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {pol : StorePol} {clob : List String}
    (h : frameCheck σ a p pol clob = true) : codeFrame σ a p + redZone + 8 ≤ 2 ^ 64 := by
  unfold frameCheck at h
  unfold codeFrame
  split at h
  · rename_i F _ _ _ hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [hc] using h.1.1.1
  · cases h

/-- **The check of a region kernel from `frameCheck`**: a kernel at the layout
    `redLayout σ F` of the frame `F` of its code, whose program, store policy and clobber set
    pass `frameCheck`, passes `ProgKernelData.check`. -/
theorem ProgKernelData.check_of_frameCheck {d : ProgKernelData} {σ : AbiLayout}
    (hl : d.layout = redLayout σ d.frame)
    (hF : d.frame = codeFrame σ (nfAbiNames d.name σ) d.prog)
    (h : frameCheck σ (nfAbiNames d.name σ) d.prog d.pol d.clob = true) : d.check = true := by
  unfold frameCheck at h
  split at h
  · rename_i F P bs ro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcomp, q, hq, hro⟩ := frameCompile_spec hc
    have hF' : d.frame = F := by rw [hF, codeFrame, hc]; rfl
    have ha : nfAbiNames d.name d.layout = nfAbiNames d.name σ := by rw [hl]; rfl
    unfold ProgKernelData.check ProgKernelData.compile
    rw [d.backProg_eq hq, regionROB_castProg, ha, hl, hF', hcomp, hro]
    simp only [h.1.1.2, h.1.2, h.2, Bool.and_self]
  · cases h

end CatCrypt.Crypto.SecureCompilation.HashTemplate
