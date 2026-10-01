/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# The canonicalised export loop node of the shipped `mpn_and_n_loop_owned` kernel

`MpnLoopBytesEmit.kernels` maps the linked symbol `mpn_and_n_loop_owned` to
`MpnLoopFrontEmit.andLprog`, which `binLprog` front-compiles from
`MpnLoopFrontEmit.binBody .SAnd` at limb count `MpnAddCarryFrontPrototype.N`
with the slots `out` / `a` / `b`. This module supplies the renaming and thread
certificates of `JasminLsemExportCanonLogic` at that body and instantiates
`JasminLsemExportCanon.canonNodeRM_faithful` there.

The renamings and certificates of `JasminLsemExportCanonLogic` §1 are parametric
in the loop depth, the store slot and the output register, so they apply to any
chain with the same four-argument layout whatever its limb count and slot names;
only the chain walk of the thread certificate is per-body.

## Main results

* `binAndUpdate` — the `JLoopBodyN.update`-shaped jasmin program the front emits
  for the shipped limb body.
* `binAndUpdate_arrMemN` — that body is in the array-returning stack-memory
  fragment.
* `binAndUpdate_threadCertT` — its thread certificate, from the accumulator
  argument to the chain's return array.
* `binAnd_canon_machine_denoteT`, `binAnd_canon_machine_denote` — the
  canonicalised node of the shipped body halts with the array at `out` decoding
  to the source fold `JLoopBodyN.denote`.

## Scope

The conclusion is at `JLoopBodyN.denote` of the shipped body. Reading that
denotation as the elementwise conjunction of the two source arrays — the step
`JasminLsemExportCanonLogic.and_canon_machine_val` takes through
`MpnLogicalFrontEmit.andFold_cells` — needs the fold identification of
`binBody`, which this module does not establish.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit (binBody vmBin ΓbodyBin)

variable (d : Nat) (out : String)

/-! ## 1. Resolved operand shapes with a chain-register index -/

/-- A single argument operand is resolved. -/
theorem threadUses_arg (j cd : Nat) (hj : j < 4) :
    ∀ n ∈ [argName j], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact resolved_argName hj

/-- A load whose array operand is an argument and whose index operand is an
    earlier chain register: both are resolved. -/
theorem threadUses_arg_reg (j k cd : Nat) (hj : j < 4) (hk : 4 ≤ k ∧ k < cd) :
    ∀ n ∈ [argName j, regName k], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact resolved_argName hj
  · exact resolved_regName hk.1 hk.2

/-- A store whose index operand is an earlier chain register — the accumulator
    argument, the index register and the stored chain register — is resolved. -/
theorem threadUses_store_reg (ki k cd : Nat) (hki : 4 ≤ ki ∧ ki < cd)
    (hk : 4 ≤ k ∧ k < cd) :
    ∀ n ∈ [argName 3, regName ki, regName k], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact resolved_argName (by omega)
  · exact resolved_regName hki.1 hki.2
  · exact resolved_regName hk.1 hk.2

/-! ## 2. The shipped limb body -/

/-- The front accepts the `mpn_and_n_loop_owned` limb body. -/
theorem binAndFrontOk :
    (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out"
      (binBody .SAnd)).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the limb
    body of `MpnLoopFrontEmit.andLprog`, the `Lprog` the seam links as
    `mpn_and_n_loop_owned`. -/
def binAndUpdate : Com jasminDialect (mapCtx ΓbodyBin) (mapTy (CryptoTy.memref N)) :=
  (frontLoopBodyJ (accCTy := CryptoTy.memref N) vmBin "out" (binBody .SAnd)).get
    binAndFrontOk

/-- The shipped limb body is in the array-returning stack-memory fragment. -/
theorem binAndUpdate_arrMemN : ArrMemN binAndUpdate := by
  unfold binAndUpdate
  repeat first
    | exact ArrMemN.ret _
    | refine ArrMemN.store rfl _ ?_
    | refine ArrMemN.reg _ ?_ ?_
    | exact ScalarMemN.load rfl _ (.ret .here)
    | exact ScalarMemN.mulhi rfl _ (.ret .here)
    | exact ScalarMemN.addLo rfl _ (.ret .here)
    | exact ScalarMemN.addHi rfl _ (.ret .here)
    | exact ScalarMemN.const _ (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.sel rfl _ (.ret .here)
    | exact ScalarMemN.shr (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.shl (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.sar (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.cast rfl _ (.ret .here)
    | exact ScalarMemN.var _ rfl _ (.ret .here)

/-! ## 3. The thread certificate and the canonicalised node -/

/-- **The thread certificate of the shipped `mpn_and_n_loop_owned` chain.** The
    chain materialises the loop index in a body temporary, loads the two source
    limbs from the invariant arrays through it, combines them and stores the
    result through the accumulator argument, so its only store result is its last
    slot and the accumulator thread head never moves before it. -/
theorem binAndUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AN, AN] : Ctxt jasminDialect).length + 2)
      (logicS 9) out
      (straightOpsMem (([AN, AN] : Ctxt jasminDialect).length + 2) binAndUpdate
        (([AN, AN] : Ctxt jasminDialect).length + 2))
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (accRegMN [AN, AN]) (loopBodyRetArrMN binAndUpdate) := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_arg 2 4 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_arg_reg 1 4 5 (by omega) (by omega)
  · exact threadArr_inv out τ 1 h1o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_arg_reg 0 4 6 (by omega) (by omega)
  · exact threadArr_inv out τ 0 h0o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 5 6 7 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 7 8 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store_reg 4 8 9 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact threadArr_acc out τ

/-- **The canonicalised shipped `mpn_and_n_loop_owned` node computes the model
    loop.** The canonicalised, aliased export loop node of the shipped limb body,
    run on the flag machine from program counter `0` with the seed agreement,
    readable invariant base registers and the trip count in `c`, halts with the
    array at `out` decoding to the source fold of that body. -/
theorem binAnd_canon_machine_denoteT (τ : String → String)
    (hτ : CanonRen τ d (([AN, AN] : Ctxt jasminDialect).length) (logicS 9) out)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = τ (argName j))
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM τ (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (τ (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM τ d out c binAndUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) :=
  canonNodeRM_faithful binAndUpdate binAndUpdate_arrMemN hτ
    (binAndUpdate_threadCertT out τ h0o h1o) absent regs hregs invs fn c hc b0 zf hpc
    arr0 hseed hinv m hm64 hcnt

/-- `binAnd_canon_machine_denoteT` at the renaming `logicTau d 9 out`, whose
    `CanonRen` certificate is `logicTau_canonRen` at the shipped chain's store
    slot. -/
theorem binAnd_canon_machine_denote
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = logicTau d 9 out (argName j))
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau d 9 out) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau d 9 out (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (logicTau d 9 out) d out c binAndUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) :=
  binAnd_canon_machine_denoteT d out _ (logicTau_canonRen d 9 out hoR hoI hoC hoA)
    (by rw [logicTau_argName_lt d 9 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 9 out (by omega)]; exact hoA 1 (by omega))
    absent regs hregs invs fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped
