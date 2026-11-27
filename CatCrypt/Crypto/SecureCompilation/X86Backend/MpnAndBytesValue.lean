/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinFrontDenote

@[expose] public section

set_option autoImplicit false

/-!
# The decoded shipped `mpn_and_n_loop_owned` against the canonicalised node

`MpnBinExportTerm` gives the decoded layout `nodeLayout andDecPre andDecLoop andDecPost` of
the function bytes of the shipped `mpn_and_n_loop_owned`.
`JasminLsemExportCanonLogicShipped.binAnd_canon_machine_denote` gives the run of the
canonicalised flag-machine node `canonNodeRM (logicTau 4 9 "a3") 4 "a3" "a2" binAndUpdate
false ["a1", "a0"]` of the shipped limb body. This module discharges the hypotheses of
`DecodedLsemLoop.decNode_halts` for that node against the decoded layout, as
`MpnMul1BytesValue` does for `mpn_mul_1`.

The canonical chain keeps the index scaling as the two-operand shift `SHL:64 d, a, #0`
(`shlImm0I`), where the export body has the count-in-mnemonic form `SHL:0:64 d, a`
(`immShiftI`); `decSim_shlImm0` simulates the two-operand form by the copy the decoded body
has, so no list equality between the two forms is needed.

## Main results

* `and_trip`: one trip of the decoded loop body simulates one limb step of the canonical node.
* `and_pre`, `and_post`: the decoded prologue and epilogue simulate those of the canonical node.
* `and_node_halts_fuel`: the decoded node halts within the fuel the canonical node needs.
* `mpn_and_n_bytes_correct`: the function bytes of the shipped `mpn_and_n_loop_owned` decode
  to the node layout, and the decoded run stores the limbwise conjunction of the two inputs.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM tripValArrMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped
  (binAndUpdate binAnd_canon_machine_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode (findLabelMem_append_of_isLopn)

/-! ## 1. The two-operand count-`0` shift -/

/-- The two-operand shift `SHL:64 d, a, #0` of the canonical chain. -/
def shlImm0I (d a : String) : LinstrRM :=
  (.Lopn [.reg d] "SHL:64" [.reg a, .imm 0], .reg none)

theorem stripWidthTag_SHL64 : stripWidthTag "SHL:64" = "SHL" := by decide +kernel

/-- `SHL:64 d, a, #0` copies `a` to `d` on the flag machine and keeps the flag. -/
theorem fstepF_shlImm0 (d a : String) (b : LstateM) (zf : Bool) (va : BitVec 64)
    (hva : b.reg.getW a 64 = some va) :
    fstepF (shlImm0I d a) b zf
      = some (withALUFlags (shlImm0I d a) b ((b.setReg d va).nextPc), zf) := by
  have hc : cmpArgs? (shlImm0I d a) = none := by
    simp only [cmpArgs?, shlImm0I]
    rw [ite_eq_right (fun h => absurd h (by decide +kernel))]
  have hm : movRegArgs? (shlImm0I d a) = none := rfl
  have hs : lsemStepMem (shlImm0I d a) b = some ((b.setReg d va).nextPc) := by
    rw [shlImm0I, lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ (by simp [mulhiStruct?]) rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne (by rw [stripWidthTag_SHL64]; decide))]
    simp only [lsemStepN, readReg_of_getW hva, evalOperandN, stripWidthTag_SHL64, applyOpnN,
      Option.map_some, BitVec.toNat_ofNat, Nat.zero_mod, shiftMask_zero, BitVec.shiftLeft_zero]
    rfl
  unfold fstepF stepMemF
  simp only [hc, hm, hs, Option.map_some]

/-- **`SHL:64 d, a, #0` against the copy `mov %a, %d`.** -/
theorem decSim_shlImm0 {π : String → String} {L L' : String → Prop} {Lay : Layout}
    {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}
    (d a : String) (ha : L a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [shlImm0I d a] [.mov (π d) (.reg (π a))] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_shlImm0 d a b zf _ (h.regs a ha),
      (h.write d (sa.regs (π a)) (evalInstrA sa (.mov (π d) (.reg (π a)))) (fun _ => rfl) rfl hL
        (fun hz => False.elim hz)).withALUFlags (shlImm0I d a) b⟩


/-- `decSim_shlImm0` with the machine registers named. -/
theorem decSim_shlImm0_r {π : String → String} {L : String → Prop} {Lay : Layout}
    {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}
    (d a D A : String) (hD : π d = D) (hA : π a = A) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [shlImm0I d a] [.mov D (.reg A)] := by
  subst hD hA
  exact decSim_shlImm0 d a ha (fun r hr => by
    rcases hr with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, h2⟩)

/-! ## 2. The canonicalised node as literals -/

/-- The straight chain of the shipped limb body: the index scaling, the two limb loads,
    the conjunction, the result scaling and the store. -/
theorem andStraight_eq : straightOpsMem 4 binAndUpdate 4 =
    [ (.Lopn [.reg (regName 4)] "SHL:64" [.reg (argName 2), .imm 0], .reg none)
    , (.Lopn [.reg (regName 5)] "LOADIDX" [.arrIdx (argName 1) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 6)] "LOADIDX" [.arrIdx (argName 0) (regName 4) 8], .load 64 4)
    , (.Lopn [.reg (regName 7)] "AND:64" [.reg (regName 5), .reg (regName 6)], .reg none)
    , (.Lopn [.reg (regName 8)] "SHL:64" [.reg (regName 7), .imm 0], .reg none)
    , (.Lopn [.reg (regName 9)] "STOREIDX" [.arrIdx (argName 3) (regName 4) 8,
        .reg (regName 8)], .store 64 4) ] := by
  kernel_rfl

/-- The renaming of the canonical node: `logicTau` at depth `4`, store slot `9` and output
    register `a3`. -/
noncomputable abbrev andTau : String → String := logicTau 4 9 "a3"

/-- The looped segment of the canonicalised node, as a literal. -/
def andLoopBodyLit : List LinstrRM :=
  [ shlImm0I "L4_r4" "Lidx4"
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8], .load 64 4)
  , (.Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a0" "L4_r4" 8], .load 64 4)
  , binRegI "AND:64" "L4_r7" "L4_r5" "L4_r6"
  , shlImm0I "L4_r8" "L4_r7"
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r4" 8, .reg "L4_r8"], .store 64 4)
  , movRI "a3" "a3"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a1")
  , cmpRI "Lctr4" (.reg "a0") ]

/-- The renamed straight chain. -/
theorem andStraightRen_eq : (straightOpsMem 4 binAndUpdate 4).map (renRM andTau) =
    andLoopBodyLit.take 6 := by
  rw [andStraight_eq]
  simp only [renRM, renLinstrR, List.map, renOperand, andTau,
    logicTau_argName2, logicTau_argName3, logicTau_regName_store,
    logicTau_regName 4 9 "a3" (k := 4) (by decide), logicTau_regName 4 9 "a3" (k := 5) (by decide),
    logicTau_regName 4 9 "a3" (k := 6) (by decide), logicTau_regName 4 9 "a3" (k := 7) (by decide),
    logicTau_regName 4 9 "a3" (k := 8) (by decide),
    logicTau_argName_lt 4 9 "a3" (j := 0) (by decide),
    logicTau_argName_lt 4 9 "a3" (j := 1) (by decide)]
  kernel_rfl

/-- **The looped segment of the canonicalised node** is `andLoopBodyLit`. -/
theorem andCanonBody_eq :
    canonBodyRM andTau 4 "a3" binAndUpdate false ["a1", "a0"] = andLoopBodyLit := by
  show (straightOpsMem 4 binAndUpdate 4).map (renRM andTau) ++ _ = _
  rw [andStraightRen_eq]
  kernel_rfl

/-- The seed moves of the canonicalised node, as a literal. -/
theorem andSeeds_eq :
    canonSeedsRM 4 "a3" "a2" = [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"] := by
  kernel_rfl

theorem loopCtr_four : loopCtr 4 = "Lctr4" := by decide +kernel

/-- **The canonicalised node** is the three seeds followed by the guarded loop over
    `andLoopBodyLit`. -/
theorem andNode_eq :
    canonNodeRM andTau 4 "a3" "a2" binAndUpdate false ["a1", "a0"]
      = [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" andLoopBodyLit := by
  unfold canonNodeRM
  rw [andSeeds_eq, andCanonBody_eq, loopCtr_four]


/-- The renamed seeds and the looped segment are all-`Lopn`. -/
theorem andSeeds_isLopn :
    ∀ i ∈ [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"], IsLopn i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

theorem andLoopBody_isLopn : ∀ i ∈ andLoopBodyLit, IsLopn i := by
  intro i hi
  simp only [andLoopBodyLit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, rfl⟩

theorem andNode_top :
    findLabelMem 4 ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" andLoopBodyLit)
      = some (3 + 2) := by
  rw [findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn, findLabelMem_guarded_top]
  simp

theorem andNode_end :
    findLabelMem (4 + 0x40000000) ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" andLoopBodyLit)
      = some (3 + andLoopBodyLit.length + 5) := by
  rw [findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_endL _ _ _ _ andLoopBody_isLopn (by decide)]
  simp only [Option.map_some, Option.some.injEq, List.length_cons, List.length_nil]
  omega

/-! ## 3. The layout and the relation along the trip -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnBinExportTerm
  (andDecPre andDecLoop andDecLoopBody andDecPost)

/-- The register assignment of the loop node: each name to the machine register the decoded
    body keeps it in. -/
def andPi (r : String) : String :=
  if r = "a3" then "%rbx" else if r = "a1" then "%rcx" else if r = "a0" then "%rdx"
  else if r = "a2" then "%rsi" else if r = "Lidx4" then "%rax" else if r = "Lctr4" then "%rdi"
  else if r = "L4_r4" then "%rsi" else if r = "L4_r5" then "%rbp" else if r = "L4_r6" then "%r8"
  else if r = "L4_r7" then "%r9" else if r = "L4_r8" then "%rbp" else r

/-- The array layout: the output `a3` at `rp`, the sources `a1` at `ap` and `a0` at `bp`,
    four words each, with their pointers in the slots `s0`, `s1`, `s2`. -/
def andLay (rp ap bp : BitVec 64) : Layout where
  base A := if A = "a1" then ap else if A = "a0" then bp else rp
  len _ := 4
  slot A := if A = "a3" then some "s0" else if A = "a1" then some "s1"
    else if A = "a0" then some "s2" else none

/-- The frame: `s0` at `56(%rsp)`, `s1` at `48(%rsp)`, `s2` at `-8(%rsp)`. -/
def andFrame (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  if q = "s0" then some (rsp + BitVec.ofInt 64 56)
  else if q = "s1" then some (rsp + BitVec.ofInt 64 48)
  else if q = "s2" then some (rsp + BitVec.ofInt 64 (-8)) else none

/-- The cells: every word of the three arrays. -/
def andK (A : String) (j : Nat) : Prop := (A = "a3" ∨ A = "a1" ∨ A = "a0") ∧ j < 4

/-- The names live at the loop head. -/
abbrev andLive (r : String) : Prop := r ∈ ["a3", "a1", "a0", "Lidx4", "Lctr4"]

/-- The names live after the index copy, after each limb load, and before the store. -/
abbrev andLiveA (r : String) : Prop := r ∈ ["L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev andLiveB (r : String) : Prop :=
  r ∈ ["L4_r5", "L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev andLiveC (r : String) : Prop :=
  r ∈ ["L4_r6", "L4_r5", "L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev andLiveD (r : String) : Prop :=
  r ∈ ["L4_r8", "L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]

/-- The machine registers the trip tracks: the stack pointer, the index in `%rax` and the
    counter in `%rdi`. -/
def andP (rsp : BitVec 64) (x y : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp ∧ sa.regs "%rax" = BitVec.ofNat 64 x ∧ sa.regs "%rdi" = BitVec.ofNat 64 y

theorem andP_runBlock (rsp : BitVec 64) (x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi"], R ∉ dsts j) (sa : AState)
    (hp : andP rsp x y sa) : andP rsp x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨by rw [e _ (by simp)]; exact hp.1, by rw [e _ (by simp)]; exact hp.2.1,
    by rw [e _ (by simp)]; exact hp.2.2⟩

/-- The loop-head relation after trip `t` of `m`. -/
def andQ (rsp : BitVec 64) (m t : Nat) (sa : AState) : Prop :=
  andP rsp (t + 1) (m - (t + 1)) sa
    ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 (m - (t + 1)) == 0#64)

section Trip

variable (rp ap bp rsp : BitVec 64)

/-- The relation along the loop trip. -/
abbrev andRel (L : String → Prop) (K : String → Nat → Prop) (zl : Prop) (P : AState → Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr andPi L (andLay rp ap bp) (andFrame rsp) K zl sa b zf ∧ P sa

/-- The trip predicate with the index copy in `%rsi`. -/
def andPI (rsp : BitVec 64) (x y i : Nat) (sa : AState) : Prop :=
  andP rsp x y sa ∧ sa.regs "%rsi" = BitVec.ofNat 64 i

theorem andPI_runBlock (rsp : BitVec 64) (x y i : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi", "%rsi"], R ∉ dsts j) (sa : AState)
    (hp : andPI rsp x y i sa) : andPI rsp x y i (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨⟨by rw [e _ (by simp)]; exact hp.1.1, by rw [e _ (by simp)]; exact hp.1.2.1,
    by rw [e _ (by simp)]; exact hp.1.2.2⟩, by rw [e _ (by simp)]; exact hp.2⟩

/-- The index copy `L4_r4 := Lidx4` into `%rsi`. -/
theorem and_seg_idx (t y : Nat) (zl : Prop) :
    DecSim (andRel rp ap bp rsp andLive andK zl (andP rsp t y))
      (andRel rp ap bp rsp andLiveA andK False (andPI rsp t y t))
      [shlImm0I "L4_r4" "Lidx4"] [.mov "%rsi" (.reg "%rax")] := by
  refine DecSim.weaken (DecSim.frame _ _ (decSim_shlImm0_r "L4_r4" "Lidx4" "%rsi" "%rax" rfl rfl
    (by decide +kernel)) (fun sa hp => ⟨andP_runBlock rsp t y _
      (by decide +kernel) sa hp, ?_⟩)) (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (by decide +kernel) id (fun _ _ h => h), h.2⟩)
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec, em]
  exact hp.2.1

/-- The load of `a1[L4_r4]` through the pointer reloaded from `48(%rsp)`. -/
theorem and_seg_load1 (t y : Nat) (ht : t < 4) :
    DecSim (andRel rp ap bp rsp andLiveA andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLiveB andK False (andPI rsp t y t))
      [(.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "L4_r4" 8], .load 64 4)]
      [.loadMem "%r14" "%rsp" 48, .loadMemIdx "%rbp" "%r14" "%rsi" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
      (π := andPi) (L := andLiveA) (L' := andLiveB)
      "L4_r5" "a1" "L4_r4" "%r14" "%rsp" "s1" 48 rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1.1]; rfl, Or.inr (Or.inl rfl), by
      show (sa.regs "%rsi").toNat < 4
      rw [hp.2, ofNat_toNat_lt t (by omega)]; exact ht⟩)
    (andPI_runBlock rsp t y t _ (by decide +kernel))

/-- The load of `a0[L4_r4]` through the pointer reloaded from `-8(%rsp)`. -/
theorem and_seg_load0 (t y : Nat) (ht : t < 4) :
    DecSim (andRel rp ap bp rsp andLiveB andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLiveC andK False (andPI rsp t y t))
      [(.Lopn [.reg "L4_r6"] "LOADIDX" [.arrIdx "a0" "L4_r4" 8], .load 64 4)]
      [.loadMem "%r14" "%rsp" (-8), .loadMemIdx "%r8" "%r14" "%rsi" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
      (π := andPi) (L := andLiveB) (L' := andLiveC)
      "L4_r6" "a0" "L4_r4" "%r14" "%rsp" "s2" (-8) rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1.1]; rfl, Or.inr (Or.inr rfl), by
      show (sa.regs "%rsi").toNat < 4
      rw [hp.2, ofNat_toNat_lt t (by omega)]; exact ht⟩)
    (andPI_runBlock rsp t y t _ (by decide +kernel))

/-- The conjunction and the result copy. -/
theorem and_seg_and (t y : Nat) :
    DecSim (andRel rp ap bp rsp andLiveC andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLiveD andK False (andPI rsp t y t))
      [binRegI "AND:64" "L4_r7" "L4_r5" "L4_r6", shlImm0I "L4_r8" "L4_r7"]
      [.mov "%r9" (.reg "%rbp"), .and_ "%r9" (.reg "%r8"), .mov "%rbp" (.reg "%r9")] := by
  refine DecSim.frame _ _ ?_ (andPI_runBlock rsp t y t _ (by decide +kernel))
  have h1 := decSim_and_mov (π := andPi) (L := andLiveC) (Lay := andLay rp ap bp)
    (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r7" "L4_r5" "L4_r6" "%r9" "%rbp" "%r8" rfl rfl rfl (by decide) (by decide +kernel)
    (by decide +kernel)
  have h2 := decSim_shlImm0_r (π := andPi) (L := liveAfter andPi andLiveC "L4_r7" "%r9")
    (Lay := andLay rp ap bp) (frame := andFrame rsp) (K := andK) (zl := False)
    "L4_r8" "L4_r7" "%rbp" "%r9" rfl rfl (Or.inl rfl)
  exact DecSim.weaken (h1.append h2) (fun _ _ _ h => h)
    (fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h))

/-- Two distinct words of one array below `4` words lie at distinct addresses. -/
theorem andLay_addr_ne (A : String) {j j' : Nat} (hj : j < 4) (hj' : j' < 4) (hne : j' ≠ j) :
    (andLay rp ap bp).addr A j' ≠ (andLay rp ap bp).addr A j := by
  intro h
  have h' := congrArg BitVec.toNat (add_left_cancel h)
  simp only [BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

/-- The output words are disjoint from the words of both sources. -/
def andDis : Prop :=
  ∀ j j', j < 4 → j' < 4 →
    Disjoint8 ((andLay rp ap bp).addr "a3" j) ((andLay rp ap bp).addr "a1" j')
      ∧ Disjoint8 ((andLay rp ap bp).addr "a3" j) ((andLay rp ap bp).addr "a0" j')

/-- The cells of `andK` survive the store to `a3[j]`. -/
theorem andK_afterStore (hdis : andDis rp ap bp) (j : Nat) (hj : j < 4) :
    ∀ A j', andK A j' → afterStore (andLay rp ap bp) andK "a3" "a3" j A j' := by
  rintro A j' ⟨hA, hj'⟩
  rcases hA with rfl | rfl | rfl
  · by_cases hjj : j' = j
    · exact Or.inl ⟨rfl, Or.inl hjj⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨⟨Or.inl rfl, hj'⟩, andLay_addr_ne rp ap bp "a3" hj hj' hjj⟩⟩
  · exact Or.inr ⟨by decide, ⟨Or.inr (Or.inl rfl), hj'⟩,
      ne_of_disjoint8 ((hdis j j' hj hj').1)⟩
  · exact Or.inr ⟨by decide, ⟨Or.inr (Or.inr rfl), hj'⟩,
      ne_of_disjoint8 ((hdis j j' hj hj').2)⟩

/-- The store of the result word to `a3[L4_r4]` through the pointer reloaded from
    `56(%rsp)`. -/
theorem and_seg_store (t y : Nat) (ht : t < 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp) :
    DecSim (andRel rp ap bp rsp andLiveD andK False (andPI rsp t y t))
      (andRel rp ap bp rsp andLiveD andK False (andP rsp t y))
      [(.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r4" 8, .reg "L4_r8"], .store 64 4)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg "%rbp")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ (andP rsp t y)
      (decSim_storeR (π := andPi) (L := andLiveD) (Lay := andLay rp ap bp)
        (frame := andFrame rsp) (K := andK) (zl := False) hsep
        "a3" "a3" "L4_r4" "L4_r8" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel) (by decide +kernel) t)
      (fun sa hp => ⟨by rw [hp.1.1]; rfl, by
        show (sa.regs "%rsi").toNat = t
        rw [hp.2, ofNat_toNat_lt t (by omega)], ⟨Or.inl rfl, ht⟩⟩)
      (fun sa hp => andP_runBlock rsp t y _ (by decide +kernel) sa hp.1))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (andK_afterStore rp ap bp hdis t ht), h.2⟩)

/-- The feedback copy, the index advance, the counter decrement and the three compares
    ending in the back-edge compare. -/
theorem and_seg_tail (m t : Nat) (htm : t < m) :
    DecSim (andRel rp ap bp rsp andLiveD andK False (andP rsp t (m - t)))
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

/-! ## 4. The trip, the guard and the loop hypotheses -/

/-- **One trip of the shipped `mpn_and_n_loop_owned` loop**, for each trip `t < m ≤ 4`. -/
theorem and_trip (m : Nat) (hm : m ≤ 4) (hsep : (andLay rp ap bp).Sep (andFrame rsp))
    (hdis : andDis rp ap bp) (t : Nat) (ht : t < m) :
    DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
      (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
      (andLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (andDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (and_seg_idx rp ap bp rsp t (m - t) False).append <|
  (and_seg_load1 rp ap bp rsp t (m - t) (by omega)).append <|
  (and_seg_load0 rp ap bp rsp t (m - t) (by omega)).append <|
  (and_seg_and rp ap bp rsp t (m - t)).append <|
  (and_seg_store rp ap bp rsp t (m - t) (by omega) hsep hdis).append <|
  and_seg_tail rp ap bp rsp m t ht

/-- The relation after the zero-trip guard `cmp %rdi, 0`. -/
def andG (m : Nat) : AState → LstateM → Bool → Prop :=
  andRel rp ap bp rsp andLive andK True
    (fun sa => andP rsp 0 m sa ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 m == 0#64))

/-- **The zero-trip guard.** -/
theorem and_guard (m : Nat) (zl : Prop) :
    DecSim (andRel rp ap bp rsp andLive andK zl (andP rsp 0 m)) (andG rp ap bp rsp m)
      [cmpRI "Lctr4" (.imm 0)] [.cmp "%rdi" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ⟨hp, ?_⟩)
  · exact decSim_cmpImm_r "Lctr4" "%rdi" 0 rfl (by decide +kernel)
  · show ZF_of_word (sa.regs "%rdi" - BitVec.ofNat 64 0) = _
    rw [hp.2.2, ZF_of_word_sub]

theorem and_guard_flag (m : Nat) (hm : m ≤ 4) :
    ∀ sa b zf, andG rp ap bp rsp m sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0) := by
  intro sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz]
  exact ofNat_beq_zero_iff m (by omega)

theorem and_guard_inv (m : Nat) :
    ∀ sa b zf pc, andG rp ap bp rsp m sa b zf →
      andRel rp ap bp rsp andLive andK False (andP rsp 0 (m - 0)) sa (b.setLpc pc) zf :=
  fun _ _ _ pc ⟨h, hp, _⟩ => ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

theorem and_trip_flag (m : Nat) (hm : m ≤ 4) :
    ∀ t, t < m → ∀ sa b zf, andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m) := by
  intro t ht sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz, ofNat_beq_zero_iff _ (by omega)]
  omega

theorem and_trip_next (m : Nat) :
    ∀ t, t < m → ∀ sa b zf pc, andRel rp ap bp rsp andLive andK True (andQ rsp m t) sa b zf →
      andRel rp ap bp rsp andLive andK False (andP rsp (t + 1) (m - (t + 1))) sa
        (b.setLpc pc) zf :=
  fun _ _ _ _ _ pc ⟨h, hp, _⟩ =>
    ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

end Trip


/-! ## 5. The prologue and the epilogue -/

/-- The register map at the entry: the four arguments in the System V argument registers,
    `rp` (`a3`) in `%rdi`, `ap` (`a1`) in `%rsi`, `bp` (`a0`) in `%rdx`, the count (`a2`) in
    `%rcx`. -/
def andPi0 (r : String) : String :=
  if r = "a3" then "%rdi" else if r = "a1" then "%rsi" else if r = "a0" then "%rdx"
  else if r = "a2" then "%rcx" else r

/-- The four argument names. -/
abbrev andArgs (r : String) : Prop := r ∈ ["a3", "a1", "a0", "a2"]

/-- The layout without pointer slots, for the entry. -/
def andLay0 (rp ap bp : BitVec 64) : Layout := { andLay rp ap bp with slot := fun _ => none }

/-- The machine state at the entry: the stack pointer `64` above the body's, the three
    pointers and the count in their argument registers. -/
def andEntry (rp ap bp rsp : BitVec 64) (m : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp + BitVec.ofInt 64 64 ∧ sa.regs "%rdi" = rp ∧ sa.regs "%rsi" = ap
    ∧ sa.regs "%rdx" = bp ∧ sa.regs "%rcx" = BitVec.ofNat 64 m

/-- The cells are disjoint from the stack words at offsets `-16` to `56` from the body's
    stack pointer. -/
def andStackSep (rp ap bp rsp : BitVec 64) : Prop :=
  ∀ A j, andK A j → ∀ o : Int, -16 ≤ o → o ≤ 56 →
    Disjoint8 (rsp + BitVec.ofInt 64 o) ((andLay rp ap bp).addr A j)

/-- The machine part of the prologue: the frame `leaq`, the ten saves and the three reloads
    of the arguments into their loop registers. -/
def andPre15 : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48, .loadMem "%rsi" "%rsp" (-16) ]

theorem andDecPre_eq : andDecPre = andPre15 ++
    [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi")] := rfl

section Pre

variable (rp ap bp rsp : BitVec 64)

/-- **The machine part of the prologue.** From the entry correspondence at `andPi0`, the
    fifteen machine instructions establish the correspondence at `andPi` for the four
    arguments, with the three pointer slots of the frame holding `rp`, `ap` and `bp`. -/
theorem and_pre15 (m : Nat) (zl : Prop) (hstk : andStackSep rp ap bp rsp) :
    DecSim (fun sa b zf => DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK
        zl sa b zf ∧ andEntry rp ap bp rsp m sa)
      (andRel rp ap bp rsp andArgs andK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      [] andPre15 := by
  refine DecSim.machBlock fun sa b zf ⟨h, hrsp, hrdi, hrsi, hrdx, hrcx⟩ => ?_
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emm : ∀ (s : AState) (X Y : String), (evalInstrA s (.mov X (.reg Y))).mem = s.mem :=
    fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-64)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 64 + BitVec.ofInt 64 (-64) = 0#64 by decide +kernel, BitVec.add_zero]
  simp only [andPre15, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  generalize hs' : evalInstrA _ (.loadMem "%rsi" "%rsp" (-16)) = s'
  have hmem := congrArg AState.mem hs'
  have hregs := fun x => congrArg (fun s => AState.regs s x) hs'
  simp (config := { decide := true }) only [em, emm, es, esm, elm, ele, elem,
    evalInstrA_loadMem_regs', ite_true, ite_false, hlea] at hmem hregs
  simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
    [read64_write64_same, read64_write64_of_disjoint] at hregs
  generalize hM : write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64
    (write64 (write64 sa.mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _ = M at hmem
  have hcell : ∀ A j, andK A j → read64 M ((andLay rp ap bp).addr A j)
      = read64 sa.mem ((andLay rp ap bp).addr A j) := by
    intro A j hk
    have hd := fun o h1 h2 => hstk A j hk o h1 h2
    rw [← hM]
    rw [read64_write64_of_disjoint _ _ _ _ (hd (-16) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (-8) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 0 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 8 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 16 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 24 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 32 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 40 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 48 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 56 (by omega) (by omega))]
  have hs0 : read64 M (rsp + BitVec.ofInt 64 56) = rp := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrdi
  have hs1 : read64 M (rsp + BitVec.ofInt 64 48) = ap := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrsi
  have hs2 : read64 M (rsp + BitVec.ofInt 64 (-8)) = bp := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrdx
  have hr : ∀ x, s'.regs x = _ := fun x => (hregs x).symm
  refine ⟨⟨fun r hr' => ?_, fun hz => hz.elim, fun A j hk => ?_, fun A q hq => ?_⟩, ?_, ?_⟩
  · simp only [andArgs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · show _ = some (s'.regs "%rbx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a3" (by decide)
    · show _ = some (s'.regs "%rcx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a1" (by decide)
    · show _ = some (s'.regs "%rdx")
      rw [hr]; simp (config := { decide := true }) only [ite_false]
      exact h.regs "a0" (by decide)
    · show _ = some (s'.regs "%rsi")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a2" (by decide)
  · obtain ⟨hj, arr, ha, hc⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [← hmem, hcell A j hk]; exact hc⟩
  · simp only [andLay] at hq
    split_ifs at hq with h0 h1 h2
    · subst h0; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs0]; rfl⟩
    · subst h1; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs1]; rfl⟩
    · subst h2; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs2]; rfl⟩
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]; exact hrcx

/-- The three loop seeds: the output touch, the index at `0` and the counter from `a2`. -/
theorem and_seg_seeds (m : Nat) :
    DecSim (andRel rp ap bp rsp andArgs andK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      (andRel rp ap bp rsp andLive andK False (andP rsp 0 m))
      [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
      [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rsi")] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ?_)
  · decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.mov X (.imm n))).regs x
        = if x = X then BitVec.ofNat 64 n else s.regs x := fun _ _ _ _ => rfl
    simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    refine ⟨?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [em, ei, ite_false]; exact hp.1
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]; exact hp.2

/-- **The prologue.** -/
theorem and_pre (m : Nat) (zl : Prop) (hstk : andStackSep rp ap bp rsp) :
    DecSim (fun sa b zf => DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK
        zl sa b zf ∧ andEntry rp ap bp rsp m sa)
      (andRel rp ap bp rsp andLive andK False (andP rsp 0 m))
      [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"] andDecPre := by
  rw [andDecPre_eq]
  exact (and_pre15 rp ap bp rsp m zl hstk).append (and_seg_seeds rp ap bp rsp m)

/-- The exit relation: the flag machine's array `a3` has the shape `(64, 4)`, and each of its
    words sits little-endian at its layout address. -/
def andOut (sa : AState) (b : LstateM) : Prop :=
  ∃ arr : Fin 4 → BitVec 64, decodeArrM b "a3" 64 4 = some arr
    ∧ ∀ j, j < 4 → read64 sa.mem ((andLay rp ap bp).addr "a3" j) = stackGet arr j

/-- **The epilogue.** The restores and the closing `leaq` write no memory. -/
theorem and_post (m : Nat) :
    ∀ sa b, andRel rp ap bp rsp andLive andK False (andP rsp m (m - m)) sa b true →
      andOut rp ap bp (aMachine.runBlock sa andDecPost) b := by
  intro sa b ⟨h, _⟩
  have hmem : (aMachine.runBlock sa andDecPost).mem = sa.mem := rfl
  obtain ⟨_, arr, ha, _⟩ := h.cells "a3" 0 ⟨Or.inl rfl, by decide⟩
  refine ⟨arr, ha, fun j hj => ?_⟩
  obtain ⟨_, arr', ha', hr⟩ := h.cells "a3" j ⟨Or.inl rfl, hj⟩
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  rw [hmem]; exact hr

end Pre

/-! ## 6. The node -/

/-- The fuel of the flag-machine run of the node at count `n`: three seeds, `13` steps for
    each pass (the `11` instructions of the looped segment, the back-edge compare and the
    branch), and four for the guard and the labels. -/
def andFuel (n : Nat) : Nat := nodeFuel 3 11 n

theorem andLoopBodyLit_length : andLoopBodyLit.length = 11 := rfl

/-- **The shipped `mpn_and_n_loop_owned` node on both machines, with its fuel.** From the
    entry correspondence at `andPi0` and the entry machine state, with the count `m ≤ 4`:
    the machine halts on the decoded layout from index `0`, the flag machine halts on the
    canonicalised node at every fuel from `andFuel m` on, and at the end the words of the
    flag machine's `a3` sit at the output addresses. -/
theorem and_node_halts_fuel (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b zf
      ∧ andEntry rp ap bp rsp m sa) :
    ∃ sa' t, Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 sa sa'
      ∧ (∀ k, andFuel m ≤ k →
          lsemFuelMemF (singletonProgM fn
            (canonNodeRM andTau 4 "a3" "a2" binAndUpdate false ["a1", "a0"])) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ andOut rp ap bp sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
        (andRel rp ap bp rsp andLive andK True (andQ rsp m t))
        (andLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
        (andDecLoop.body ++ [andDecLoop.cmpInstr]) := by
    intro t ht
    exact and_trip rp ap bp rsp m hm hsep hdis t ht
  have hg : DecSim (andRel rp ap bp rsp andLive andK False (andP rsp 0 m)) (andG rp ap bp rsp m)
      [cmpRI "Lctr4" (.imm 0)] [andDecLoop.cmpInstr] :=
    and_guard rp ap bp rsp m False
  rw [andNode_eq]
  exact decNode_halts_fuel fn [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
    andLoopBodyLit 4 (4 + 0x40000000) "Lctr4" andDecLoop m _ _ (andG rp ap bp rsp m)
    (fun t => andRel rp ap bp rsp andLive andK False (andP rsp t (m - t)))
    (fun t => andRel rp ap bp rsp andLive andK True (andQ rsp m t)) (andOut rp ap bp)
    andDecPre andDecPost andSeeds_isLopn andLoopBody_isLopn andNode_top andNode_end
    (and_pre rp ap bp rsp m False hstk) hg (and_guard_flag rp ap bp rsp m hm)
    (and_guard_inv rp ap bp rsp m) hsim (and_trip_flag rp ap bp rsp m hm)
    (and_trip_next rp ap bp rsp m) (and_post rp ap bp rsp m) sa b zf hpc hE


/-! ## 7. The decoded bytes compute the model loop -/

theorem a3_ne_loopReg (k : Nat) : "a3" ≠ loopReg 4 k := argName_ne_loopReg 4 3 k

/-- **The decoded shipped `mpn_and_n_loop_owned` computes the source fold.** From an entry
    state of the machine with the three pointers, the count `m ≤ 4` and the stack pointer
    in their argument registers, and a flag-machine state `b0` that corresponds to it
    (`andPi0`) and agrees with the valuation `invs` of the two source arrays and the output
    seed `arr0` (`hseed`, the seed agreement of `binAnd_canon_machine_denote`): the machine
    halts on the decoded layout of the shipped object's function bytes, and the four words
    at `rp` are the words of `JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0`. -/
theorem and_decoded_denote (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
    (hsep : (andLay rp ap bp).Sep (andFrame rsp)) (hdis : andDis rp ap bp)
    (hstk : andStackSep rp ap bp rsp)
    (fn : String) (sa : AState) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hE : DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa b0 zf
      ∧ andEntry rp ap bp rsp m sa)
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect)) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM andTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN invs 0 arr0)) :
    ∃ sa', Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 sa sa'
      ∧ ∀ j, j < 4 → read64 sa'.mem ((andLay rp ap bp).addr "a3" j)
          = stackGet (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) j := by
  obtain ⟨sa', t1, hh, hrun1, arr, ha, hw⟩ :=
    and_node_halts_fuel rp ap bp rsp m hm hsep hdis hstk fn sa b0 zf hpc hE
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
  obtain ⟨k, t2, hrun2, hdec⟩ := binAnd_canon_machine_denote 4 "a3" a3_ne_loopReg
    (by decide +kernel) (by decide +kernel)
    (fun j hj => by
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl <;> decide +kernel)
    false ["a1", "a0"] hregs invs fn "a2" (by decide +kernel) b0 zf hpc arr0 hseed hinv m
    (by omega) hcnt
  have he : t1 = t2 := lsemFuelMemF_det _ _ _ _ _ _ (hrun1 _ (Nat.le_refl _)) hrun2
  subst he
  have hd : decodeArrM t1.prog.base "a3" 64 4
      = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) := hdec
  rw [ha] at hd
  obtain rfl := Option.some.inj hd
  exact ⟨sa', hh, hw⟩


/-! ## 8. The word-level result -/

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit (logicFold logicFold_get)

/-- **The decoded shipped `mpn_and_n_loop_owned` writes the conjunction.** Under the
    hypotheses of `and_decoded_denote` with the source valuation `(a, b)` (the words at `ap`
    and at `bp`): the machine halts on the decoded layout of the shipped object's function
    bytes, and for every `j < m` the word at `rp + 8 j` is `a[j] &&& b[j]`. -/
theorem and_decoded_val (rp ap bp rsp : BitVec 64) (m : Nat) (hm : m ≤ 4)
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
    ∃ sa', Halts aMachine (nodeLayout andDecPre andDecLoop andDecPost) 0 sa sa'
      ∧ ∀ j, j < m → read64 sa'.mem ((andLay rp ap bp).addr "a3" j)
          = memGetDyn a j &&& memGetDyn b j := by
  obtain ⟨sa', hh, hw⟩ := and_decoded_denote rp ap bp rsp m hm hsep hdis hstk fn sa b0 zf hpc
    hE (.cons a (.cons b .nil)) arr0 hseed
  have key := MpnBinFrontDenote.binAnd_denote MpnBinExportTerm.andFront_eq a b arr0 m (by omega)
  refine ⟨sa', hh, fun j hj => ?_⟩
  rw [hw j (by omega)]
  refine (congrArg (fun x => stackGet x j) key).trans ?_
  rw [DialectToJasminComCorrect.stackGet_eq_memGetDyn]
  exact logicFold_get _ a b arr0 m hm j hj


/-! ## 9. The linked object -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)

/-- **`mpn_and_n_loop_owned`, from the linked program to its result words.** The program
    `MpnLoopFrontEmit.andLprog ()` that `MpnLoopBytesEmit.kernels` maps to the linked symbol is
    one function `mpn_and_n_loop_owned`; the function bytes the byte encoder lays down for its
    body (the `text` of the object, `MpnBinExportTerm.andObjBytes_eq`) decode to a program
    `prog`; and from every entry state with `rp`, `ap`, `bp` and the count `m ≤ 4` in
    `%rdi`, `%rsi`, `%rdx`, `%rcx`, the three arrays of four words pairwise separated from
    each other and from the frame, and a flag-machine state corresponding to it and agreeing
    with the source words `a` at `ap` and `b` at `bp` (the hypotheses of `and_decoded_val`),
    the machine halts on `prog` with `a[j] &&& b[j]` at `rp + 8 j` for every `j < m`. -/
theorem mpn_and_n_bytes_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.andLprog ()).map (·.lp_funcs) = some [("mpn_and_n_loop_owned", f)]
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
              = memGetDyn a j &&& memGetDyn b j := by
  obtain ⟨f, hf, hdec⟩ := MpnBinExportTerm.andLprog_decode
  refine ⟨f, hf, _, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa b0 zf hpc hE hent
    a b arr0 hseed => ?_⟩
  obtain ⟨sa', hh, hw⟩ := and_decoded_val rp ap bp rsp m hm hsep hdis hstk
    "mpn_and_n_loop_owned" sa b0 zf hpc
    ⟨hE, hent⟩ a b arr0 hseed
  exact ⟨sa', hh, fun j hj => hw j hj⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
