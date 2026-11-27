/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue

@[expose] public section

set_option autoImplicit false

/-!
# The decoded shipped `mpn_xor_n_loop_owned` writes the exclusive-or

The xor kernel's canonical chain and decoded loop differ from the and kernel's only in the
combiner (`XOR:64` for `AND:64`, `xor` for `and`). This module instantiates
`canonNodeRM_faithful` at the shipped xor body (the certificates are the and body's, word for
word), states the canonical node as a literal, and reuses every op-independent segment of
`MpnAndBytesValue` (layout, prologue, loads, store, tail, guard, epilogue) for the machine chain.

## Main results

* `binXor_canon_machine_denote` — the canonicalised node of the shipped xor body computes the
  source fold.
* `xor_node_halts_fuel`, `xor_decoded_val` — the decoded shipped object against that node, and
  the exclusive-or of the source words at the output.
* `mpn_xor_n_bytes_correct` — from the linked program to its result words.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnXorBytesValue

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped
  (threadUses_arg threadUses_arg_reg threadUses_store_reg)
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit (binBody vmBin ΓbodyBin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm (binXorUpdate)

variable (d : Nat) (out : String)

/-! ## 1. The canonicalised node of the shipped xor body -/

/-- The shipped limb body is in the array-returning stack-memory fragment. -/
theorem binXorUpdate_arrMemN : ArrMemN binXorUpdate := by
  unfold binXorUpdate
  repeat first
    | exact ArrMemN.ret _
    | refine ArrMemN.store rfl _ ?_
    | refine ArrMemN.reg _ ?_ ?_
    | exact ScalarMemN.load rfl _ (.ret .here)
    | exact ScalarMemN.shl (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.var _ rfl _ (.ret .here)



/-- **The thread certificate of the shipped `mpn_xor_n_loop_owned` chain.** The
    chain materialises the loop index in a body temporary, loads the two source
    limbs from the invariant arrays through it, combines them and stores the
    result through the accumulator argument, so its only store result is its last
    slot and the accumulator thread head never moves before it. -/
theorem binXorUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AN, AN] : Ctxt jasminDialect).length + 2)
      (logicS 9) out
      (straightOpsMem (([AN, AN] : Ctxt jasminDialect).length + 2) binXorUpdate
        (([AN, AN] : Ctxt jasminDialect).length + 2))
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (accRegMN [AN, AN]) (loopBodyRetArrMN binXorUpdate) := by
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

/-- **The canonicalised shipped `mpn_xor_n_loop_owned` node computes the model
    loop.** The canonicalised, aliased export loop node of the shipped limb body,
    run on the flag machine from program counter `0` with the seed agreement,
    readable invariant base registers and the trip count in `c`, halts with the
    array at `out` decoding to the source fold of that body. -/
theorem binXor_canon_machine_denoteT (τ : String → String)
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
          (canonNodeRM τ d out c binXorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binXorUpdate⟩ invs arr0) :=
  canonNodeRM_faithful binXorUpdate binXorUpdate_arrMemN hτ
    (binXorUpdate_threadCertT out τ h0o h1o) absent regs hregs invs fn c hc b0 zf hpc
    arr0 hseed hinv m hm64 hcnt

/-- `binXor_canon_machine_denoteT` at the renaming `logicTau d 9 out`, whose
    `CanonRen` certificate is `logicTau_canonRen` at the shipped chain's store
    slot. -/
theorem binXor_canon_machine_denote
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
          (canonNodeRM (logicTau d 9 out) d out c binXorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binXorUpdate⟩ invs arr0) :=
  binXor_canon_machine_denoteT d out _ (logicTau_canonRen d 9 out hoR hoI hoC hoA)
    (by rw [logicTau_argName_lt d 9 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 9 out (by omega)]; exact hoA 1 (by omega))
    absent regs hregs invs fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt



/-! ## 2. The canonicalised node as literals -/

theorem xorStraight_eq : straightOpsMem 4 binXorUpdate 4 =
    [ (.Lopn [.reg (regName 4)] "SHL:64" [.reg (argName 2), .imm 0], .reg none)
    , (.Lopn [.reg (regName 5)] "LOADIDX" [.arrIdx (argName 1) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 6)] "LOADIDX" [.arrIdx (argName 0) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 7)] "XOR:64" [.reg (regName 5), .reg (regName 6)], .reg none)
    , (.Lopn [.reg (regName 8)] "SHL:64" [.reg (regName 7), .imm 0], .reg none)
    , (.Lopn [.reg (regName 9)] "STOREIDX" [.arrIdx (argName 3) (regName 4) 8,
        .reg (regName 8)], .store 64 4) ] := by
  kernel_rfl

/-- The looped segment of the canonicalised xor node, as a literal. -/
def xorLoopBodyLit : List LinstrRM :=
  [ shlImm0I "L4_r4" "Lidx4"
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8], .load 64 4)
  , (.Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a0" "L4_r4" 8], .load 64 4)
  , binRegI "XOR:64" "L4_r7" "L4_r5" "L4_r6"
  , shlImm0I "L4_r8" "L4_r7"
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r4" 8, .reg "L4_r8"], .store 64 4)
  , movRI "a3" "a3"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a1")
  , cmpRI "Lctr4" (.reg "a0") ]

theorem xorStraightRen_eq : (straightOpsMem 4 binXorUpdate 4).map (renRM andTau) =
    xorLoopBodyLit.take 6 := by
  rw [xorStraight_eq]
  simp only [renRM, renLinstrR, List.map, renOperand, andTau,
    logicTau_argName2, logicTau_argName3, logicTau_regName_store,
    logicTau_regName 4 9 "a3" (k := 4) (by decide), logicTau_regName 4 9 "a3" (k := 5) (by decide),
    logicTau_regName 4 9 "a3" (k := 6) (by decide), logicTau_regName 4 9 "a3" (k := 7) (by decide),
    logicTau_regName 4 9 "a3" (k := 8) (by decide),
    logicTau_argName_lt 4 9 "a3" (j := 0) (by decide),
    logicTau_argName_lt 4 9 "a3" (j := 1) (by decide)]
  kernel_rfl

theorem xorCanonBody_eq :
    canonBodyRM andTau 4 "a3" binXorUpdate false ["a1", "a0"] = xorLoopBodyLit := by
  show (straightOpsMem 4 binXorUpdate 4).map (renRM andTau) ++ _ = _
  rw [xorStraightRen_eq]
  kernel_rfl

theorem xorNode_eq :
    canonNodeRM andTau 4 "a3" "a2" binXorUpdate false ["a1", "a0"]
      = [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" xorLoopBodyLit := by
  unfold canonNodeRM
  rw [andSeeds_eq, xorCanonBody_eq, loopCtr_four]

theorem xorLoopBody_isLopn : ∀ i ∈ xorLoopBodyLit, IsLopn i := by
  intro i hi
  simp only [xorLoopBodyLit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl⟩

theorem xorNode_top :
    findLabelMem 4 ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" xorLoopBodyLit)
      = some (3 + 2) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_top]
  simp

theorem xorNode_end :
    findLabelMem (4 + 0x40000000) ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" xorLoopBodyLit)
      = some (3 + xorLoopBodyLit.length + 5) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_endL _ _ _ _ xorLoopBody_isLopn (by decide)]
  simp only [Option.map_some, Option.some.injEq, List.length_cons, List.length_nil]
  omega


/-! ## 3. The machine chain -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
  (andDecPre andDecPost xorDecPre xorDecLoop xorDecLoopBody xorDecPost)

theorem xorDecPre_eq : xorDecPre = andDecPre := rfl
theorem xorDecPost_eq : xorDecPost = andDecPost := rfl

section Trip

variable (rp ap bp rsp : BitVec 64)

/-- The exclusive-or and the result copy. -/
theorem xor_seg_op (t y : Nat) :
    DecSim (andRel rp ap bp rsp andLiveC andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLiveD andK False (andPI rsp t y t))
      [binRegI "XOR:64" "L4_r7" "L4_r5" "L4_r6", shlImm0I "L4_r8" "L4_r7"]
      [.mov "%r9" (.reg "%rbp"), .xor_ "%r9" (.reg "%r8"), .mov "%rbp" (.reg "%r9")] := by
  refine DecSim.frame _ _ ?_ (andPI_runBlock rsp t y t _ (by decide +kernel))
  have h1 := decSim_xor_mov (π := andPi) (L := andLiveC) (Lay := andLay rp ap bp)
    (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r7" "L4_r5" "L4_r6" "%r9" "%rbp" "%r8" rfl rfl rfl (by decide) (by decide +kernel)
    (by decide +kernel)
  have h2 := decSim_shlImm0_r (π := andPi) (L := liveAfter andPi andLiveC "L4_r7" "%r9")
    (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r8" "L4_r7" "%rbp" "%r9" rfl rfl (Or.inl rfl)
  exact DecSim.weaken (h1.append h2) (fun _ _ _ h => h)
    (fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h))

/-- **One trip of the shipped `mpn_xor_n_loop_owned` loop.** -/
theorem xor_trip (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (t : Nat) (ht : t < m) :
    DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
      (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
      (xorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (xorDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (and_seg_idx rp ap bp rsp t (m - t) False).append <|
  (and_seg_load1 rp ap bp rsp t (m - t) (by omega)).append <|
  (and_seg_load0 rp ap bp rsp t (m - t) (by omega)).append <|
  (xor_seg_op rp ap bp rsp t (m - t)).append <|
  (and_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis).append <|
  and_seg_tail rp ap bp rsp m t ht

end Trip

/-- **The shipped `mpn_xor_n_loop_owned` node on both machines, with its fuel.** -/
theorem xor_node_halts_fuel (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b zf
      ∧ andEntry rp ap bp rsp m sa) :
    ∃ sa' t, Halts aMachine (nodeLayout xorDecPre xorDecLoop xorDecPost) 0 sa sa'
      ∧ (∀ k, andFuel m ≤ k →
          lsemFuelMemF (singletonProgM fn
            (canonNodeRM andTau 4 "a3" "a2" binXorUpdate false ["a1", "a0"])) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ andOut rp ap bp sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
        (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
        (xorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
        (xorDecLoop.body ++ [xorDecLoop.cmpInstr]) := by
    intro t ht
    exact xor_trip rp ap bp rsp m hm hsep hdis t ht
  have hg : DecSim (andRel rp ap bp rsp andLive andK False (andP rsp 0 m)) (andG rp ap bp rsp m)
      [cmpRI "Lctr4" (.imm 0)] [xorDecLoop.cmpInstr] :=
    and_guard rp ap bp rsp m False
  rw [xorNode_eq, xorDecPre_eq, xorDecPost_eq]
  exact decNode_halts_fuel fn [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
    xorLoopBodyLit 4 (4 + 0x40000000) "Lctr4" xorDecLoop m _ _ (andG rp ap bp rsp m)
    (fun t => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
    (fun t => andRel rp ap bp rsp andLive andK True (andQ rsp m t)) (andOut rp ap bp)
    andDecPre andDecPost andSeeds_isLopn xorLoopBody_isLopn xorNode_top xorNode_end
    (and_pre rp ap bp rsp m False hstk) hg (and_guard_flag rp ap bp rsp m hm)
    (and_guard_inv rp ap bp rsp m) hsim (and_trip_flag rp ap bp rsp m hm)
    (and_trip_next rp ap bp rsp m) (and_post rp ap bp rsp m) sa b zf hpc hE

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit (logicFold logicFold_get)

/-- **The decoded shipped `mpn_xor_n_loop_owned` writes the exclusive-or.** -/
theorem xor_decoded_val (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b0 zf
      ∧ andEntry rp ap bp rsp m sa)
    (a b arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM andTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AN, AN] : Ctxt jasminDialect)) (.cons a (.cons b .nil)) 0 arr0)) :
    ∃ sa', Halts aMachine (nodeLayout xorDecPre xorDecLoop xorDecPost) 0 sa sa'
      ∧ ∀ j, j < m → read64 sa'.mem ((andLay rp ap bp).addr "a3" j)
          = memGetDyn a j ^^^ memGetDyn b j := by
  obtain ⟨sa', t1, hh, hrun1, arr, ha, hw⟩ :=
    xor_node_halts_fuel rp ap bp rsp m hm hsep hdis hstk fn sa b0 zf hpc hE
  have hregs : ∀ r ∈ ["a1", "a0"], ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = logicTau 4 9 "a3" (argName j) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨1, by decide, by rw [logicTau_argName_lt 4 9 "a3" (by decide)]; rfl⟩
    · exact ⟨0, by decide, by rw [logicTau_argName_lt 4 9 "a3" (by decide)]; rfl⟩
  have hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau 4 9 "a3" (argName j)) 64).isSome := by
    intro j hj
    rw [logicTau_argName_lt 4 9 "a3" hj]
    have hj2 : j = 0 ∨ j = 1 := by
      have : j < 2 := hj
      omega
    rcases hj2 with rfl | rfl
    · rw [show argName 0 = "a0" from rfl, hE.1.regs "a0" (by decide)]; rfl
    · rw [show argName 1 = "a1" from rfl, hE.1.regs "a1" (by decide)]; rfl
  have hcnt : b0.reg.getW "a2" 64 = some (BitVec.ofNat 64 m) := by
    rw [hE.1.regs "a2" (by decide)]
    exact congrArg some hE.2.2.2.2.2
  obtain ⟨k, t2, hrun2, hdec⟩ := binXor_canon_machine_denote 4 "a3" a3_ne_loopReg
    (by decide +kernel) (by decide +kernel)
    (fun j hj => by
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl <;> decide +kernel)
    false ["a1", "a0"] hregs (.cons a (.cons b .nil)) fn "a2" (by decide +kernel) b0 zf hpc
    arr0 hseed hinv m (by omega) hcnt
  have he : t1 = t2 := lsemFuelMemF_det _ _ _ _ _ _ (hrun1 _ (Nat.le_refl _)) hrun2
  subst he
  have hd : decodeArrM t1.prog.base "a3" 64 4
      = some (JLoopBodyN.denote ⟨m, binXorUpdate⟩ (.cons a (.cons b .nil)) arr0) := hdec
  rw [ha] at hd
  obtain rfl := Option.some.inj hd
  have key := MpnBinFrontDenote.binXor_denote MpnBinExportTerm.xorFront_eq a b arr0 m (by omega)
  refine ⟨sa', hh, fun j hj => ?_⟩
  rw [hw j (by omega)]
  refine (congrArg (fun x => stackGet x j) key).trans ?_
  rw [DialectToJasminComCorrect.stackGet_eq_memGetDyn]
  exact logicFold_get _ a b arr0 m hm j hj

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)

/-- **`mpn_xor_n_loop_owned`, from the linked program to its result words.** As
    `MpnAndBytesValue.mpn_and_n_bytes_correct`, with `a[j] ^^^ b[j]`. -/
theorem mpn_xor_n_bytes_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs) = some [("mpn_xor_n_loop_owned", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ (sa : AState) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
        DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b0 zf →
        andEntry rp ap bp rsp m sa →
        ∀ (a b arr0 : Fin N → BitVec 64),
        StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
          (([AN, AN] : Ctxt jasminDialect).length + 2)
          (pullM andTau (b0.setReg (loopIdx 4) (0#64)))
          (tripValArrMN (invTys := ([AN, AN] : Ctxt jasminDialect)) (.cons a (.cons b .nil)) 0
            arr0) →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ ∀ j, j < m → read64 sa'.mem (rp + BitVec.ofNat 64 (8 * j))
              = memGetDyn a j ^^^ memGetDyn b j := by
  refine ⟨_, by rw [MpnBinExportTerm.xorLprog_eq]; rfl, nodeLayout xorDecPre xorDecLoop xorDecPost,
    ?_, fun rp ap bp rsp m hm hsep hdis
    hstk sa b0 zf hpc hE hent a b arr0 hseed => ?_⟩
  · rw [MpnBinExportTerm.xorPhysAbi_eq]
    exact MpnBinExportTerm.xorPhysLit_decode
  · obtain ⟨sa', hh, hw⟩ := xor_decoded_val rp ap bp rsp m hm hsep hdis hstk
      "mpn_xor_n_loop_owned" sa b0 zf hpc ⟨hE, hent⟩ a b arr0 hseed
    exact ⟨sa', hh, fun j hj => hw j hj⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnXorBytesValue
