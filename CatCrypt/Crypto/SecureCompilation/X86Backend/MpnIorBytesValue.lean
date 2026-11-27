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
# The decoded shipped `mpn_ior_n_loop_owned` writes the disjunction

The ior kernel computes `a OR b` as `(a XOR b) XOR (a AND b)`: its canonical chain has three
combiner instructions (store slot `11`) and its decoded loop keeps the four results in `%r9`,
`%r10`, `%rbp`, `%r8`. This module instantiates `canonNodeRM_faithful` at the shipped ior body
with its own thread certificate, states the canonical node as a literal, and builds the machine
chain on a register map `iorPi` that agrees with `MpnAndBytesValue.andPi` on the names live at
the loop head, so the prologue, the loads, the guard and the epilogue of `MpnAndBytesValue` are
reused through `DecLsemCorr.congrPi`.

## Main results

* `binIor_canon_machine_denote` — the canonicalised node of the shipped ior body computes the
  source fold.
* `ior_node_halts_fuel`, `ior_decoded_val` — the decoded shipped object against that node, and
  the disjunction of the source words at the output.
* `mpn_ior_n_bytes_correct` — from the linked program to its result words.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnIorBytesValue

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm (binIorUpdate)

variable (d : Nat) (out : String)

/-! ## 1. The canonicalised node of the shipped ior body -/

/-- The shipped limb body is in the array-returning stack-memory fragment. -/
theorem binIorUpdate_arrMemN : ArrMemN binIorUpdate := by
  unfold binIorUpdate
  repeat first
    | exact ArrMemN.ret _
    | refine ArrMemN.store rfl _ ?_
    | refine ArrMemN.reg _ ?_ ?_
    | exact ScalarMemN.load rfl _ (.ret .here)
    | exact ScalarMemN.shl (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.var _ rfl _ (.ret .here)



/-- **The thread certificate of the shipped `mpn_ior_n_loop_owned` chain.** The
    chain materialises the loop index in a body temporary, loads the two source
    limbs from the invariant arrays through it, combines them and stores the
    result through the accumulator argument, so its only store result is its last
    slot and the accumulator thread head never moves before it. -/
theorem binIorUpdate_threadCertT (τ : String → String)
    (h0o : τ (argName 0) ≠ out) (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AN, AN] : Ctxt jasminDialect).length + 2)
      (logicS 11) out
      (straightOpsMem (([AN, AN] : Ctxt jasminDialect).length + 2) binIorUpdate
        (([AN, AN] : Ctxt jasminDialect).length + 2))
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (accRegMN [AN, AN]) (loopBodyRetArrMN binIorUpdate) := by
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
  · exact threadUses_regs 5 6 8 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_regs 7 8 9 (by omega) (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [logicS], ?_⟩⟩
  · exact threadUses_reg 9 10 (by omega)
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · exact threadUses_store_reg 4 10 11 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact threadArr_acc out τ

/-- **The canonicalised shipped `mpn_ior_n_loop_owned` node computes the model
    loop.** The canonicalised, aliased export loop node of the shipped limb body,
    run on the flag machine from program counter `0` with the seed agreement,
    readable invariant base registers and the trip count in `c`, halts with the
    array at `out` decoding to the source fold of that body. -/
theorem binIor_canon_machine_denoteT (τ : String → String)
    (hτ : CanonRen τ d (([AN, AN] : Ctxt jasminDialect).length) (logicS 11) out)
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
          (canonNodeRM τ d out c binIorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binIorUpdate⟩ invs arr0) :=
  canonNodeRM_faithful binIorUpdate binIorUpdate_arrMemN hτ
    (binIorUpdate_threadCertT out τ h0o h1o) absent regs hregs invs fn c hc b0 zf hpc
    arr0 hseed hinv m hm64 hcnt

/-- `binIor_canon_machine_denoteT` at the renaming `logicTau d 11 out`, whose
    `CanonRen` certificate is `logicTau_canonRen` at the shipped chain's store
    slot. -/
theorem binIor_canon_machine_denote
    (hoR : ∀ k, out ≠ loopReg d k) (hoI : out ≠ loopIdx d) (hoC : out ≠ loopCtr d)
    (hoA : ∀ j, j < 2 → argName j ≠ out)
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = logicTau d 11 out (argName j))
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau d 11 out) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau d 11 out (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM (logicTau d 11 out) d out c binIorUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out 64 N
            = some (JLoopBodyN.denote ⟨m, binIorUpdate⟩ invs arr0) :=
  binIor_canon_machine_denoteT d out _ (logicTau_canonRen d 11 out hoR hoI hoC hoA)
    (by rw [logicTau_argName_lt d 11 out (by omega)]; exact hoA 0 (by omega))
    (by rw [logicTau_argName_lt d 11 out (by omega)]; exact hoA 1 (by omega))
    absent regs hregs invs fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt




/-! ## 2. The canonicalised node as literals -/

theorem iorStraight_eq : straightOpsMem 4 binIorUpdate 4 =
    [ (.Lopn [.reg (regName 4)] "SHL:64" [.reg (argName 2), .imm 0], .reg none)
    , (.Lopn [.reg (regName 5)] "LOADIDX" [.arrIdx (argName 1) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 6)] "LOADIDX" [.arrIdx (argName 0) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 7)] "XOR:64" [.reg (regName 5), .reg (regName 6)], .reg none)
    , (.Lopn [.reg (regName 8)] "AND:64" [.reg (regName 5), .reg (regName 6)], .reg none)
    , (.Lopn [.reg (regName 9)] "XOR:64" [.reg (regName 7), .reg (regName 8)], .reg none)
    , (.Lopn [.reg (regName 10)] "SHL:64" [.reg (regName 9), .imm 0], .reg none)
    , (.Lopn [.reg (regName 11)] "STOREIDX" [.arrIdx (argName 3) (regName 4) 8,
        .reg (regName 10)], .store 64 4) ] := by
  kernel_rfl

/-- The renaming of the canonical ior node: `logicTau` at store slot `11`. -/
noncomputable abbrev iorTau : String → String := logicTau 4 11 "a3"

/-- The looped segment of the canonicalised ior node, as a literal. -/
def iorLoopBodyLit : List LinstrRM :=
  [ shlImm0I "L4_r4" "Lidx4"
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8], .load 64 4)
  , (.Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a0" "L4_r4" 8], .load 64 4)
  , binRegI "XOR:64" "L4_r7" "L4_r5" "L4_r6"
  , binRegI "AND:64" "L4_r8" "L4_r5" "L4_r6"
  , binRegI "XOR:64" "L4_r9" "L4_r7" "L4_r8"
  , shlImm0I "L4_r10" "L4_r9"
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r4" 8, .reg "L4_r10"], .store 64 4)
  , movRI "a3" "a3"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a1")
  , cmpRI "Lctr4" (.reg "a0") ]

theorem iorStraightRen_eq : (straightOpsMem 4 binIorUpdate 4).map (renRM iorTau) =
    iorLoopBodyLit.take 8 := by
  rw [iorStraight_eq]
  simp only [renRM, renLinstrR, List.map, renOperand, iorTau,
    logicTau_argName2, logicTau_argName3, logicTau_regName_store,
    logicTau_regName 4 11 "a3" (k := 4) (by decide), logicTau_regName 4 11 "a3" (k := 5) (by decide), logicTau_regName 4 11 "a3" (k := 6) (by decide), logicTau_regName 4 11 "a3" (k := 7) (by decide), logicTau_regName 4 11 "a3" (k := 8) (by decide), logicTau_regName 4 11 "a3" (k := 9) (by decide), logicTau_regName 4 11 "a3" (k := 10) (by decide),
    logicTau_argName_lt 4 11 "a3" (j := 0) (by decide),
    logicTau_argName_lt 4 11 "a3" (j := 1) (by decide)]
  kernel_rfl

theorem iorCanonBody_eq :
    canonBodyRM iorTau 4 "a3" binIorUpdate false ["a1", "a0"] = iorLoopBodyLit := by
  show (straightOpsMem 4 binIorUpdate 4).map (renRM iorTau) ++ _ = _
  rw [iorStraightRen_eq]
  kernel_rfl

theorem iorNode_eq :
    canonNodeRM iorTau 4 "a3" "a2" binIorUpdate false ["a1", "a0"]
      = [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" iorLoopBodyLit := by
  unfold canonNodeRM
  rw [andSeeds_eq, iorCanonBody_eq, loopCtr_four]

theorem iorLoopBody_isLopn : ∀ i ∈ iorLoopBodyLit, IsLopn i := by
  intro i hi
  simp only [iorLoopBodyLit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl⟩

theorem iorNode_top :
    findLabelMem 4 ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" iorLoopBodyLit)
      = some (3 + 2) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_top]
  simp

theorem iorNode_end :
    findLabelMem (4 + 0x40000000) ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" iorLoopBodyLit)
      = some (3 + iorLoopBodyLit.length + 5) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_endL _ _ _ _ iorLoopBody_isLopn (by decide)]
  simp only [Option.map_some, Option.some.injEq, List.length_cons, List.length_nil]
  omega


/-! ## 3. The machine chain -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
  (andDecPre andDecPost iorDecPre iorDecLoop iorDecLoopBody iorDecPost)

theorem iorDecPre_eq : iorDecPre = andDecPre := rfl
theorem iorDecPost_eq : iorDecPost = andDecPost := rfl

/-- The register map of the ior loop: `andPi`, except the three combiner results and the
    result copy. -/
def iorPi (r : String) : String :=
  if r = "L4_r8" then "%r10" else if r = "L4_r9" then "%rbp"
  else if r = "L4_r10" then "%r8" else andPi r

/-- The correspondence depends on the register map only at the live names. -/
theorem DecLsemCorr.congrPi {π π' : String → String} {L : String → Prop} {Lay : Layout}
    {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}
    {sa : AState} {b : LstateM} {zf : Bool} (hπ : ∀ r, L r → π r = π' r)
    (h : DecLsemCorr π L Lay frame K zl sa b zf) : DecLsemCorr π' L Lay frame K zl sa b zf where
  regs r hr := by rw [← hπ r hr]; exact h.regs r hr
  zfEq := h.zfEq
  cells := h.cells
  slots := h.slots

/-- The names live before the ior store. -/
abbrev iorLiveD (r : String) : Prop :=
  r ∈ ["L4_r10", "L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]

section Trip

variable (rp ap bp rsp : BitVec 64)

/-- The relation along the ior trip, at `iorPi`. -/
abbrev iorRel (L : String → Prop) (K : String → Nat → Prop) (zl : Prop) (P : AState → Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr iorPi L (andLay rp ap bp) (andFrame rsp) K zl sa b zf ∧ P sa

/-- The three combiner instructions and the result copy. -/
theorem ior_seg_op (t y : Nat) :
    DecSim (andRel rp ap bp rsp andLiveC andK False (andPI rsp t y t))
      (iorRel rp ap bp rsp iorLiveD andK False (andPI rsp t y t))
      [binRegI "XOR:64" "L4_r7" "L4_r5" "L4_r6", binRegI "AND:64" "L4_r8" "L4_r5" "L4_r6",
        binRegI "XOR:64" "L4_r9" "L4_r7" "L4_r8", shlImm0I "L4_r10" "L4_r9"]
      [.mov "%r9" (.reg "%rbp"), .xor_ "%r9" (.reg "%r8"), .mov "%r10" (.reg "%rbp"),
        .and_ "%r10" (.reg "%r8"), .mov "%rbp" (.reg "%r9"), .xor_ "%rbp" (.reg "%r10"),
        .mov "%r8" (.reg "%rbp")] := by
  refine DecSim.frame _ _ ?_ (andPI_runBlock rsp t y t _ (by decide +kernel))
  have h1 := decSim_xor_mov (π := iorPi) (L := andLiveC) (Lay := andLay rp ap bp)
    (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r7" "L4_r5" "L4_r6" "%r9" "%rbp" "%r8" rfl rfl rfl (by decide) (by decide +kernel)
    (by decide +kernel)
  have h2 := decSim_and_mov (π := iorPi) (L := liveAfter iorPi andLiveC "L4_r7" "%r9")
    (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r8" "L4_r5" "L4_r6" "%r10" "%rbp" "%r8" rfl rfl rfl (by decide) (by decide +kernel)
    (by decide +kernel)
  have h3 := decSim_xor_mov (π := iorPi)
    (L := liveAfter iorPi (liveAfter iorPi andLiveC "L4_r7" "%r9") "L4_r8" "%r10")
    (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r9" "L4_r7" "L4_r8" "%rbp" "%r9" "%r10" rfl rfl rfl (by decide) (by decide +kernel)
    (by decide +kernel)
  have h4 := decSim_shlImm0_r (π := iorPi)
    (L := liveAfter iorPi (liveAfter iorPi (liveAfter iorPi andLiveC "L4_r7" "%r9") "L4_r8"
      "%r10") "L4_r9" "%rbp")
    (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r10" "L4_r9" "%r8" "%rbp" rfl rfl (Or.inl rfl)
  exact DecSim.weaken (h1.append (h2.append (h3.append h4)))
    (fun _ _ _ h => DecLsemCorr.congrPi (by decide +kernel) h)
    (fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h))

/-- The store of the result word to `a3[L4_r4]` from `%r8`, back to the loop-head names at
    `andPi`. -/
theorem ior_seg_store (t y : Nat) (ht : t < 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp) :
    DecSim (iorRel rp ap bp rsp iorLiveD andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLive andK False (andP rsp t y))
      [(.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r4" 8, .reg "L4_r10"], .store 64 4)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ (andP rsp t y)
      (decSim_storeR (π := iorPi) (L := iorLiveD) (Lay := andLay rp ap bp)
        (frame := andFrame rsp) (K := andK) (zl := False) hsep
        "a3" "a3" "L4_r4" "L4_r10" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel) (by decide +kernel) t)
      (fun sa hp => ⟨by rw [hp.1.1]; rfl, by
        show (sa.regs "%rsi").toNat = t
        rw [hp.2, ofNat_toNat_lt t (by omega)], ⟨Or.inl rfl, ht⟩⟩)
      (fun sa hp => andP_runBlock rsp t y _ (by decide +kernel) sa hp.1))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨DecLsemCorr.congrPi (by decide +kernel)
      (h.1.mono (L' := andLive) (by decide +kernel) id (andK_afterStore rp ap bp hdis t ht)), h.2⟩)

/-- The feedback copy, the index advance, the counter decrement and the three compares,
    from the loop-head names. -/
theorem ior_seg_tail (m t : Nat) (htm : t < m) :
    DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
      (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
      [movRI "a3" "a3", addImmI "Lidx4" "Lidx4" 1, subImmI "Lctr4" "Lctr4" 1,
        cmpRI "Lctr4" (.reg "a1"), cmpRI "Lctr4" (.reg "a0"), cmpRI "Lctr4" (.imm 0)]
      [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1),
        .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rdx"), .cmp "%rdi" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ?_)
  · decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ea : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.add X (.imm k))).regs x
        = if x = X then s.regs X + BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
    have es : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.sub X (.imm k))).regs x
        = if x = X then s.regs X - BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
    have ec : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.cmp X o)).regs
        = s.regs := fun _ _ _ => rfl
    have ez : ∀ (s : AState) (X : String) (k : Nat),
        (evalInstrA s (.cmp X (.imm k))).flags.zf.getD false
          = ZF_of_word (s.regs X - BitVec.ofNat 64 k) := fun _ _ _ => rfl
    have hm : m - t = m - (t + 1) + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := hp
    rw [show aMachine.runBlock sa [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1),
        .sub "%rdi" (.imm 1), .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rdx"),
        .cmp "%rdi" (.imm 0)]
      = evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
        (.mov "%rbx" (.reg "%rbx"))) (.add "%rax" (.imm 1))) (.sub "%rdi" (.imm 1)))
        (.cmp "%rdi" (.reg "%rcx"))) (.cmp "%rdi" (.reg "%rdx"))) (.cmp "%rdi" (.imm 0))
      from rfl]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_false]
      exact h1
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h2]; exact (BitVec.ofNat_add t 1).symm
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel]
    · rw [ez]
      simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel, ZF_of_word_sub]

/-- **One trip of the shipped `mpn_ior_n_loop_owned` loop.** -/
theorem ior_trip (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (t : Nat) (ht : t < m) :
    DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
      (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
      (iorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (iorDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (and_seg_idx rp ap bp rsp t (m - t) False).append <|
  (and_seg_load1 rp ap bp rsp t (m - t) (by omega)).append <|
  (and_seg_load0 rp ap bp rsp t (m - t) (by omega)).append <|
  (ior_seg_op rp ap bp rsp t (m - t)).append <|
  (ior_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis).append <|
  ior_seg_tail rp ap bp rsp m t ht

end Trip

/-- The fuel of the flag-machine run of the ior node at count `n`: `13` instructions per pass. -/
def iorFuel (n : Nat) : Nat := nodeFuel 3 13 n

/-- **The shipped `mpn_ior_n_loop_owned` node on both machines, with its fuel.** -/
theorem ior_node_halts_fuel (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b zf
      ∧ andEntry rp ap bp rsp m sa) :
    ∃ sa' t, Halts aMachine (nodeLayout iorDecPre iorDecLoop iorDecPost) 0 sa sa'
      ∧ (∀ k, iorFuel m ≤ k →
          lsemFuelMemF (singletonProgM fn
            (canonNodeRM iorTau 4 "a3" "a2" binIorUpdate false ["a1", "a0"])) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ andOut rp ap bp sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
        (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
        (iorLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
        (iorDecLoop.body ++ [iorDecLoop.cmpInstr]) := by
    intro t ht
    exact ior_trip rp ap bp rsp m hm hsep hdis t ht
  have hg : DecSim (andRel rp ap bp rsp andLive andK False (andP rsp 0 m)) (andG rp ap bp rsp m)
      [cmpRI "Lctr4" (.imm 0)] [iorDecLoop.cmpInstr] :=
    and_guard rp ap bp rsp m False
  rw [iorNode_eq, iorDecPre_eq, iorDecPost_eq]
  exact decNode_halts_fuel fn [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
    iorLoopBodyLit 4 (4 + 0x40000000) "Lctr4" iorDecLoop m _ _ (andG rp ap bp rsp m)
    (fun t => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
    (fun t => andRel rp ap bp rsp andLive andK True (andQ rsp m t)) (andOut rp ap bp)
    andDecPre andDecPost andSeeds_isLopn iorLoopBody_isLopn iorNode_top iorNode_end
    (and_pre rp ap bp rsp m False hstk) hg (and_guard_flag rp ap bp rsp m hm)
    (and_guard_inv rp ap bp rsp m) hsim (and_trip_flag rp ap bp rsp m hm)
    (and_trip_next rp ap bp rsp m) (and_post rp ap bp rsp m) sa b zf hpc hE

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit (logicFold logicFold_get)

/-- **The decoded shipped `mpn_ior_n_loop_owned` writes the disjunction.** -/
theorem ior_decoded_val (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b0 zf
      ∧ andEntry rp ap bp rsp m sa)
    (a b arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM iorTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AN, AN] : Ctxt jasminDialect)) (.cons a (.cons b .nil)) 0 arr0)) :
    ∃ sa', Halts aMachine (nodeLayout iorDecPre iorDecLoop iorDecPost) 0 sa sa'
      ∧ ∀ j, j < m → read64 sa'.mem ((andLay rp ap bp).addr "a3" j)
          = memGetDyn a j ||| memGetDyn b j := by
  obtain ⟨sa', t1, hh, hrun1, arr, ha, hw⟩ :=
    ior_node_halts_fuel rp ap bp rsp m hm hsep hdis hstk fn sa b0 zf hpc hE
  have hregs : ∀ r ∈ ["a1", "a0"], ∃ j, j < ([AN, AN] : Ctxt jasminDialect).length ∧
      r = logicTau 4 11 "a3" (argName j) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨1, by decide, by rw [logicTau_argName_lt 4 11 "a3" (by decide)]; rfl⟩
    · exact ⟨0, by decide, by rw [logicTau_argName_lt 4 11 "a3" (by decide)]; rfl⟩
  have hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW (logicTau 4 11 "a3" (argName j)) 64).isSome := by
    intro j hj
    rw [logicTau_argName_lt 4 11 "a3" hj]
    have hj2 : j = 0 ∨ j = 1 := by
      have : j < 2 := hj
      omega
    rcases hj2 with rfl | rfl
    · rw [show argName 0 = "a0" from rfl, hE.1.regs "a0" (by decide)]; rfl
    · rw [show argName 1 = "a1" from rfl, hE.1.regs "a1" (by decide)]; rfl
  have hcnt : b0.reg.getW "a2" 64 = some (BitVec.ofNat 64 m) := by
    rw [hE.1.regs "a2" (by decide)]
    exact congrArg some hE.2.2.2.2.2
  obtain ⟨k, t2, hrun2, hdec⟩ := binIor_canon_machine_denote 4 "a3" a3_ne_loopReg
    (by decide +kernel) (by decide +kernel)
    (fun j hj => by
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl <;> decide +kernel)
    false ["a1", "a0"] hregs (.cons a (.cons b .nil)) fn "a2" (by decide +kernel) b0 zf hpc
    arr0 hseed hinv m (by omega) hcnt
  have he : t1 = t2 := lsemFuelMemF_det _ _ _ _ _ _ (hrun1 _ (Nat.le_refl _)) hrun2
  subst he
  have hd : decodeArrM t1.prog.base "a3" 64 4
      = some (JLoopBodyN.denote ⟨m, binIorUpdate⟩ (.cons a (.cons b .nil)) arr0) := hdec
  rw [ha] at hd
  obtain rfl := Option.some.inj hd
  have key := MpnBinFrontDenote.binIor_denote MpnBinExportTerm.iorFront_eq a b arr0 m (by omega)
  refine ⟨sa', hh, fun j hj => ?_⟩
  rw [hw j (by omega)]
  refine (congrArg (fun x => stackGet x j) key).trans ?_
  rw [DialectToJasminComCorrect.stackGet_eq_memGetDyn]
  exact logicFold_get _ a b arr0 m hm j hj

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)

/-- **`mpn_ior_n_loop_owned`, from the linked program to its result words.** As
    `MpnAndBytesValue.mpn_and_n_bytes_correct`, with `a[j] ||| b[j]`. -/
theorem mpn_ior_n_bytes_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs) = some [("mpn_ior_n_loop_owned", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ (sa : AState) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
        DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b0 zf →
        andEntry rp ap bp rsp m sa →
        ∀ (a b arr0 : Fin N → BitVec 64),
        StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
          (([AN, AN] : Ctxt jasminDialect).length + 2)
          (pullM iorTau (b0.setReg (loopIdx 4) (0#64)))
          (tripValArrMN (invTys := ([AN, AN] : Ctxt jasminDialect)) (.cons a (.cons b .nil)) 0
            arr0) →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ ∀ j, j < m → read64 sa'.mem (rp + BitVec.ofNat 64 (8 * j))
              = memGetDyn a j ||| memGetDyn b j := by
  refine ⟨_, by rw [MpnBinExportTerm.iorLprog_eq]; rfl, nodeLayout iorDecPre iorDecLoop iorDecPost,
    ?_, fun rp ap bp rsp m hm hsep hdis
    hstk sa b0 zf hpc hE hent a b arr0 hseed => ?_⟩
  · rw [MpnBinExportTerm.iorPhysAbi_eq]
    exact MpnBinExportTerm.iorPhysLit_decode
  · obtain ⟨sa', hh, hw⟩ := ior_decoded_val rp ap bp rsp m hm hsep hdis hstk
      "mpn_ior_n_loop_owned" sa b0 zf hpc ⟨hE, hent⟩ a b arr0 hseed
    exact ⟨sa', hh, fun j hj => hw j hj⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnIorBytesValue
