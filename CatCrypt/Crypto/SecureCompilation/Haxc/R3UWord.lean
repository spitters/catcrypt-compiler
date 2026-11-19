/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkedKernel

/-!
# The data of linked word kernels

The data `LinkedFn.calleeData` of a linked kernel (`LinkedKernel`) whose parameters are
`u64` words or integers and whose result is a `u64` word returns its result in a register,
has no array argument, and has general-purpose argument names. The result type excludes the
shape `out` of the kernel, so its code has the shape `ins`: the layout `InsLayout` gives the
register result and the general-purpose names, and the parameter kinds of the layout, which
are the kinds `linkedKinds` of the parameter types, are scalars.

## Main results

* `LinkedKernel.calleeData_word`: the three facts at one linked kernel.
* `calleeData_word_of_kernels`: the three facts at every data of the linked functions of a
  module whose linked functions are linked kernels with word parameters and a word result.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.R3UWord

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc (CalleeData linkedKinds kindOfTy)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)

/-- The parameter kind of a `u64` word parameter and of an integer parameter is a scalar. -/
theorem kindOfTy_word_or_int {t : NfTy} (h : t = .word 64 ∨ t = .int) :
    kindOfTy (CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom.mapTy
      (CatCrypt.Crypto.Hax.NFToCat.catTy t)) = .scalar := by
  rcases h with rfl | rfl <;> rfl

/-- **The data of a linked word kernel.** The data `c` of a linked kernel whose parameters
    are `u64` words or integers and whose result is a `u64` word returns its result in a
    register, has no array argument, and has general-purpose argument names. -/
theorem LinkedKernel.calleeData_word {l : LinkedFn} (K : LinkedKernel l) {c : CalleeData}
    (hc : l.calleeData = some c)
    (hpar : (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64) :
    (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
      ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true := by
  rcases (K.code c hc).1 with ⟨hL, -⟩ | ⟨po, n, -, hres⟩
  · obtain ⟨hr, -, -, -, hcaa⟩ := regCallee_facts hc hL.result
    refine ⟨hr, ?_, ?_⟩
    · rw [hcaa, ← K.kinds c hc]
      apply CatCrypt.Crypto.Hax.insArrArgs_of_scalars
      intro k hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact kindOfTy_word_or_int (hpar.1 p hp)
    · intro a ha
      rw [← CalleeData.ins_map_fst] at ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hL.ins_gp p hp
  · rw [hpar.2] at hres
    cases hres

/-- **The data of the linked functions of a module of linked word kernels.** When every
    linked function of the module is a linked kernel with `u64` word or integer parameters
    and a `u64` word result, every data `LinkedFn.calleeData` of its linked functions returns
    its result in a register, has no array argument, and has general-purpose argument
    names: the hypothesis `hword` of `NFCallTreeR3TypedAns.r3FA_of_shape_int` from its
    hypotheses `hk` and `hpar`. -/
theorem calleeData_word_of_kernels {m : HaxModule} (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hpar : ∀ l ∈ m.linked,
      (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64) :
    ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true := by
  intro c hc
  obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp hc
  exact LinkedKernel.calleeData_word (hk l hl) hlc (hpar l hl)

end CatCrypt.Crypto.SecureCompilation.Haxc.R3UWord
