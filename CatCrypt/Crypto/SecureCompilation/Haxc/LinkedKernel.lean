/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain

@[expose] public section

set_option autoImplicit false

/-!
# Linked kernels and the contract of their record

A linked kernel (`LinkedKernel`) is a linked function whose code, at the data `c` the region
back half reads, has one of two shapes (`KernelShape`): scalars and read-only word arrays
with a word result in a register, or scalars and word arrays with the words of a
destination array as result; and whose code meets the fixed contract `LinkedFn.contract` of
its record (`LinkedFn.Meets`). The contract gives the interface of the contract at every
argument and result names (`LinkedKernel.calleeSpec_code`), and the oracle of that interface
answers within the oracle of the data (`LinkedKernel.haltsO_sig`), through the call-site
precondition of the kernel (`pre_of_callSite`).

A linked word kernel (`RegionLinkCall.LinkedWordKernel`) with a `u64` result meets its
contract (`LinkedWordKernel.meets`) and is a linked kernel of the shape `ins` with scalar
parameters only (`LinkedWordKernel.toKernel`).

## Main results

* `pre_of_callSite`: the precondition of the record at an entry state of the contract.
* `LinkedWordKernel.meets`: a linked word kernel with a `u64` result meets its contract.
* `KernelShape`, `LinkedKernel`: the two shapes of the code of a linked function, and the
  linked functions whose code has a shape and meets its contract.
* `LinkedKernel.contract_code`, `LinkedKernel.calleeSpec_code`, `LinkedKernel.haltsO_sig`: the
  decoded code of a linked kernel meets the contract and its interface, and the oracle of
  the interface answers within the oracle guarded by the precondition of the data.
* `insLayout_of_wordLayout`, `LinkedWordKernel.toKernel`: a word layout as a layout on scalar
  parameters, and a linked word kernel with a `u64` result as a linked kernel.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LinkedFnMeets

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc (CalleeData)
open CatCrypt.Crypto.Hax (LinkedFn)

/-- **The precondition of the record at an entry state of the contract.** At a state
    satisfying the precondition of the contract, the call-site precondition of `l` at the
    definedness of the meaning gives the precondition of `l`. -/
theorem pre_of_callSite {l : LinkedFn}
    (h : l.CallSitePre fun vals => (l.sem vals).isSome = true) {a : CallVar} {s : AState}
    (hs : (l.contractPre a).holds s) : l.pre s :=
  h a s (entryAt_of_pre hs) (sem_isSome_of_pre hs)

/-- **A linked word kernel with a `u64` result meets its contract.** At the data `c` of the
    region back half, the code of the kernel meets the word interface with a footprint among
    the frame bytes, and the call-site precondition gives the precondition of the record at
    every entry state of the contract. -/
theorem LinkedWordKernel.meets {l : LinkedFn} (K : LinkedWordKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) (hres : l.res = .word 64) : l.Meets := by
  obtain ⟨-, -, -, -, hframe, hbytes, -⟩ := LinkedFn.calleeData_eq hc
  obtain ⟨q, hq, hX, hF⟩ := K.code c hc
  rw [hbytes] at hq
  rw [hframe] at hF
  exact meets_of_wordSig (K.layout c hc) (fun v hv => hres ▸ hv)
    (fun _ _ hs => pre_of_callSite K.callSite hs) hq hX hF

end CatCrypt.Crypto.SecureCompilation.Haxc.LinkedFnMeets

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (WordLayout wordSig)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSpec HaltsO oracleAt runOf InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SContract)
open CatCrypt.Crypto.Hax (LinkedFn)

/-- The shape of the code of a linked function at its data `c`: scalars and read-only word
    arrays with a word result in the register of `c.resReg` (a word kernel has scalars only),
    or scalars and word arrays with the `n` words of the destination at `po` as result. -/
inductive KernelShape (l : LinkedFn) (c : CalleeData) : Prop
  | ins (hL : X86Backend.ImageAddrCallArrChain.InsLayout l c.ins c.resReg)
      (hres : arrLen? l.res = none)
  | out (po : String) (n : Nat) (hL : X86Backend.LinkedFnCallee.OutLayout l c.ins po n)
      (hres : arrLen? l.res = some n)

/-- **A linked kernel**: a linked function whose meaning returns values only on arguments of
    its parameter kinds, whose precondition holds under the resources of every call at whose
    arguments the meaning is defined, which has as many parameters as its layout has
    arguments, distinct argument registers and a frame that with the return word fits below
    `2 ^ 64`, and which, when the region back half reads its data `c`, has the parameter
    kinds of its layout, a shape, and code that meets its contract. -/
structure LinkedKernel (l : LinkedFn) : Prop where
  /-- The result is no slice. -/
  res_slice : ∀ t, l.res ≠ .slice t
  /-- The meaning returns values only on arguments of the parameter kinds. -/
  sem_kinds : ∀ vals v, l.sem vals = some v → vals.map valKind = linkedKinds l
  /-- At the data of the function, the parameter kinds are the kinds of the layout. -/
  kinds : ∀ c, l.calleeData = some c → linkedKinds l = l.layout.args.map (·.kind)
  /-- As many parameters as arguments of the layout. -/
  arity : l.params.length = l.layout.args.length
  /-- The argument registers of the layout are distinct. -/
  args_nodup : (l.layout.args.map (·.reg)).Nodup
  /-- The frame and the return word fit below `2 ^ 64`. -/
  frame_fit : l.frame + 8 ≤ 2 ^ 64
  /-- The precondition holds under the resources of every call at whose arguments the
      meaning is defined. -/
  callSite : l.CallSitePre fun vals => (l.sem vals).isSome = true
  /-- At the data of the function, a shape, and code that meets the contract. -/
  code : ∀ c, l.calleeData = some c → KernelShape l c ∧ l.Meets

/-- **The decoded code of a linked kernel meets its contract**: the code of its data decodes
    to a block whose leaky runs under `ctRegime` meet `LinkedFn.contract`. -/
theorem LinkedKernel.contract_code {l : LinkedFn} (K : LinkedKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) :
    ∃ q, decodeLprog c.bytes = some q ∧ SContract (runOf ctRegime q) l.contract := by
  obtain ⟨q, hq, hC⟩ := (K.code c hc).2.code
  refine ⟨q, ?_, hC⟩
  rw [(LinkedFn.calleeData_eq hc).2.2.2.2.2.1]
  exact hq

/-- **The decoded code of a linked kernel meets the interface of its contract**, at every
    argument names and result name. -/
theorem LinkedKernel.calleeSpec_code {l : LinkedFn} (K : LinkedKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) (args : List String) (res : Option String) :
    ∃ q, decodeLprog c.bytes = some q ∧ CalleeSpec (runOf ctRegime q) (l.contractSig args res) := by
  obtain ⟨q, hq, hC⟩ := K.contract_code hc
  exact ⟨q, hq, calleeSpec_of_sContract hC args res⟩

/-- **The oracle of the interface of the contract answers within the oracle of the data**:
    a calling body that halts with its call answered by the runs of `X` guarded by the
    precondition of `l.contractSig c.args c.res.reg?` halts with its call answered by the
    runs of `X` guarded by the precondition of `c.sig`, the precondition of `l`, which the
    call-site precondition gives (`pre_of_callSite`). -/
theorem LinkedKernel.haltsO_sig {l : LinkedFn} (K : LinkedKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) {X : CalleeRun} {pc : List RInstr} {sa sa' : AState}
    (h : HaltsO aMachine (oracleAt pc.length (guarded (l.contractSig c.args c.res.reg?) X))
      pc 0 sa sa') :
    HaltsO aMachine (oracleAt pc.length (guarded c.sig X)) pc 0 sa sa' := by
  have hcpre := (LinkedFn.calleeData_eq hc).2.2.2.2.2.2.1
  refine h.mono fun i s s' ho => ?_
  obtain ⟨hi, tr, ⟨a, ha⟩, hrn⟩ := ho
  refine ⟨hi, tr, ?_, hrn⟩
  show c.pre s
  rw [hcpre]
  exact LinkedFnMeets.pre_of_callSite K.callSite ha

/-- **A word layout is a layout on scalar parameters**: the word layout at the names `ws`
    and the result name `res`, with a footprint among the `frame` bytes below the entry
    stack register, is the layout on the parameters `ws`, each a scalar. -/
theorem insLayout_of_wordLayout {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res) (hF : ∀ s x, l.foot s x → InFrame (s.regs "%rsp") l.frame x) :
    InsLayout l (ws.map fun w => (w, ArgKind.scalar)) res where
  args := by rw [hL.args, List.map_map]; rfl
  result := hL.result
  ins_gp := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
    exact hL.ws_gp w hw
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  foot := hF

/-- The parameter kinds of a word layout at the names `ws` are scalars, one per name. -/
theorem kinds_of_wordLayout {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res) :
    l.layout.args.map (·.kind) = ws.map fun _ => ArgKind.scalar := by
  have h := congrArg (List.map Prod.snd) hL.args
  simpa [List.map_map, Function.comp_def] using h

/-- **A linked word kernel with a `u64` result is a linked kernel** of the shape `ins` with
    scalar parameters only: its data has the parameters of its argument names, each a scalar
    (`insLayout_of_wordLayout`), and its code meets its contract (`LinkedWordKernel.meets`),
    when its layout has distinct argument registers and its frame and return word fit below
    `2 ^ 64`. -/
theorem LinkedWordKernel.toKernel {l : LinkedFn} (K : LinkedWordKernel l)
    (hres : l.res = .word 64) (hnd : (l.layout.args.map (·.reg)).Nodup)
    (hfb : l.frame + 8 ≤ 2 ^ 64) : LinkedKernel l where
  args_nodup := hnd
  frame_fit := hfb
  res_slice := K.res_slice
  sem_kinds := K.sem_kinds
  kinds c hc := by
    have hk := kinds_of_wordLayout (K.layout c hc)
    have hlen := congrArg List.length hk
    rw [hk]
    unfold linkedKinds
    apply List.ext_getElem
    · simp only [List.length_map] at hlen ⊢
      rw [K.arity, hlen]
    · intro i h1 h2
      simp only [List.getElem_map]
      exact K.params_scalar _ (List.getElem_mem _)
  arity := K.arity
  callSite := K.callSite
  code c hc := by
    obtain ⟨-, -, -, -, hframe, -, -, -, -, -, -, harr⟩ := LinkedFn.calleeData_eq hc
    have hL := K.layout c hc
    have hins : c.ins = c.args.map fun w => (w, ArgKind.scalar) := by
      have hn : c.arrArgs = fun _ => none := by
        rw [harr]
        apply CatCrypt.Crypto.Hax.insArrArgs_of_scalars
        intro k hk
        rw [kinds_of_wordLayout hL] at hk
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hk
        rfl
      unfold CalleeData.ins
      rw [hn]
      apply List.ext_getElem <;> simp
    obtain ⟨-, -, -, hF⟩ := K.code c hc
    refine ⟨.ins ?_ (by rw [hres]; rfl), LinkedFnMeets.LinkedWordKernel.meets K hc hres⟩
    rw [hins]
    exact insLayout_of_wordLayout hL fun s x hx => hframe ▸ hF s x hx

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
