/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripShift

@[expose] public section

set_option autoImplicit false

/-!
# The decoded shipped `mpn_shift_rt` against the canonicalised node

`MpnRtExportTerm` gives the decoded layout of the function bytes of the shipped
`mpn_shift_rt` (`MpnShiftFrontEmit.shiftRtLprogOpt`). Its limb body
`MpnShiftFrontDenote.shiftUpdate` stores twice: the low word to `rp[i]` through the
accumulator and the high word to `rp[i + 1]` through the first store's result, the thread
head. The canonicalisation pass sends both store results to the output register, so the
renaming `shiftTau` has two store slots (`15` and `19`) where the logic family's
`logicTau` has one; `shiftCanonRen` is its `CanonRen` certificate and
`shiftUpdate_threadCertT` the thread certificate of the chain.

## Main results

* `shift_canon_machine_denote` — the canonicalised node of the shipped shift body computes
  the source fold.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit (Gouter AR AU r64 NRS NUS)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote (shiftUpdate)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripShift (shiftUpdate_arrMemN)

/-! ## 1. The two-slot renaming -/

/-- The renaming of the canonical shift node at depth `4` and output register `a3`: the
    first store result `r15` to `a3`, every other name as `logicTau 4 19 "a3"` (the second
    store result `r19` to `a3`). -/
noncomputable def shiftTau (r : String) : String :=
  if r = regName 15 then "a3" else logicTau 4 19 "a3" r

theorem shiftTau_r15 : shiftTau (regName 15) = "a3" := by simp [shiftTau]

theorem shiftTau_ne15 {r : String} (h : r ≠ regName 15) : shiftTau r = logicTau 4 19 "a3" r := by
  simp [shiftTau, h]

theorem argName_ne_r15 (j : Nat) : argName j ≠ regName 15 :=
  fun h => JasminLsemSimulation.regName_ne_argName 15 j h.symm

theorem shiftTau_r19 : shiftTau (regName 19) = "a3" := by
  rw [shiftTau_ne15 (fun h => by
    have := JasminLsemSimulation.regName_injective h; omega), logicTau_regName_store]

theorem shiftTau_reg {k : Nat} (h15 : k ≠ 15) (h19 : k ≠ 19) :
    shiftTau (regName k) = loopReg 4 k := by
  rw [shiftTau_ne15 (fun h => h15 (JasminLsemSimulation.regName_injective h)),
    logicTau_regName 4 19 "a3" h19]

theorem shiftTau_arg (j : Nat) : shiftTau (argName j) = logicTau 4 19 "a3" (argName j) :=
  shiftTau_ne15 (argName_ne_r15 j)

theorem a3_ne_loopReg (k : Nat) : "a3" ≠ loopReg 4 k := argName_ne_loopReg 4 3 k

/-- The store-slot set of the shift chain. -/
def shiftS (k : Nat) : Prop := k = 15 ∨ k = 19

/-- **The renaming certificate of the shift chain.** -/
theorem shiftCanonRen : CanonRen shiftTau 4 2 shiftS "a3" where
  fix := by
    rw [shiftTau_ne15 (fun h => absurd h.symm (ne_empty_of_head? (head?_regName 15)))]
    exact logicTauG_empty 4 19 "a3" (argName 0) (argName 1)
  tmp := by
    intro k _ hS
    exact shiftTau_reg (fun h => hS (Or.inl h)) (fun h => hS (Or.inr h))
  thr := by
    intro k _ hS
    rcases hS with rfl | rfl
    · exact shiftTau_r15
    · exact shiftTau_r19
  arg := by
    intro j k hj
    rw [shiftTau_arg]
    interval_cases j
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact argName_ne_loopReg 4 0 k
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact argName_ne_loopReg 4 1 k
    · rw [logicTau_argName2]; exact loopIdx_ne_loopReg 4 4 k
    · rw [logicTau_argName3]; exact a3_ne_loopReg k
  outL := a3_ne_loopReg
  acc := by rw [shiftTau_arg, logicTau_argName3]
  idx := by rw [shiftTau_arg, logicTau_argName2]
  ctr := by
    rw [shiftTau_ne15 (loopCtr_ne_regName 4 15)]
    exact logicTauG_loopCtr 4 19 "a3" (argName 0) (argName 1)
  argOut := by
    intro j hj
    rw [shiftTau_arg]
    interval_cases j
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; decide
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; decide
    · rw [logicTau_argName2]; decide
  invIdx := by
    intro j hj
    rw [shiftTau_arg]
    interval_cases j
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact (loopIdx_ne_argName 4 0).symm
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact (loopIdx_ne_argName 4 1).symm
  invCtr := by
    intro j hj
    rw [shiftTau_arg]
    interval_cases j
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact (loopCtr_ne_argName 4 0).symm
    · rw [logicTau_argName_lt 4 19 "a3" (by decide)]; exact (loopCtr_ne_argName 4 1).symm
  outIdx := by decide
  outCtr := by decide
  idxCtr := loopIdx_ne_loopCtr 4
  ctrL := loopCtr_ne_loopReg 4 4


/-! ## 2. The thread certificate and the canonicalised node -/

theorem res_nil (cd : Nat) : ∀ n ∈ ([] : List String), Resolved 4 cd n := by simp

theorem res_one (x : String) (cd : Nat) (hx : Resolved 4 cd x) :
    ∀ n ∈ [x], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn; exact hx

theorem res_two (x y : String) (cd : Nat) (hx : Resolved 4 cd x) (hy : Resolved 4 cd y) :
    ∀ n ∈ [x, y], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact hx
  · exact hy

theorem res_three (x y z : String) (cd : Nat) (hx : Resolved 4 cd x) (hy : Resolved 4 cd y)
    (hz : Resolved 4 cd z) : ∀ n ∈ [x, y, z], Resolved 4 cd n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hz

theorem resA (j cd : Nat) (hj : j < 4) : Resolved 4 cd (argName j) := resolved_argName hj
theorem resR (k cd : Nat) (hk : 4 ≤ k) (hk' : k < cd) : Resolved 4 cd (regName k) :=
  resolved_regName hk hk'

theorem thrNone (h : String) (τ : String → String) (out : String) :
    ∀ b, (none : Option String) = some b → τ b = out → b = h := by
  intro b hb
  cases hb

theorem thrHead (h : String) (τ : String → String) (out : String) :
    ∀ b, some h = some b → τ b = out → b = h := by
  intro b hb _
  cases hb; rfl

/-- The straight chain of the shipped shift body. -/
theorem shiftStraight_eq :
    straightOpsMem (([AU, r64] : Ctxt jasminDialect).length + 2) shiftUpdate
        (([AU, r64] : Ctxt jasminDialect).length + 2) =
    [ (.Lopn [.reg (regName 4)] "LOADIDX" [.arrIdx (argName 3) (argName 2) 8], .load 64 9)
    , (.Lopn [.reg (regName 5)] "LOADIDX" [.arrIdx (argName 1) (argName 2) 8], .load 64 8)
    , (.Lopn [.reg (regName 6)] "MOV:64" [.imm 64], .reg none)
    , (.Lopn [.reg (regName 7)] "SUB:64" [.reg (regName 6), .reg (argName 0)], .reg none)
    , (.Lopn [.reg (regName 8)] "SHL:64" [.reg (regName 7), .imm 0], .reg none)
    , (.Lopn [.reg (regName 9)] "SHL:64" [.reg (regName 5), .reg (argName 0)], .reg none)
    , (.Lopn [.reg (regName 10)] "SHL:64" [.reg (regName 9), .imm 0], .reg none)
    , (.Lopn [.reg (regName 11)] "SHR:64" [.reg (regName 5), .reg (regName 8)], .reg none)
    , (.Lopn [.reg (regName 12)] "SHL:64" [.reg (regName 11), .imm 0], .reg none)
    , (.Lopn [.reg (regName 13)] "ADD:64" [.reg (regName 10), .reg (regName 4)], .reg none)
    , (.Lopn [.reg (regName 14)] "SHL:64" [.reg (regName 13), .imm 0], .reg none)
    , (.Lopn [.reg (regName 15)] "STOREIDX" [.arrIdx (argName 3) (argName 2) 8,
        .reg (regName 14)], .store 64 9)
    , (.Lopn [.reg (regName 16)] "MOV:64" [.imm 1], .reg none)
    , (.Lopn [.reg (regName 17)] "ADD:64" [.reg (argName 2), .reg (regName 16)], .reg none)
    , (.Lopn [.reg (regName 18)] "SHL:64" [.reg (regName 17), .imm 0], .reg none)
    , (.Lopn [.reg (regName 19)] "STOREIDX" [.arrIdx (regName 15) (regName 18) 8,
        .reg (regName 12)], .store 64 9) ] := by
  kernel_rfl

/-- **The thread certificate of the shipped shift chain.** The two limb loads read the
    accumulator and the source through the argument names, the low word is stored through
    the accumulator (head `r15` after it) and the high word through `r15` (head `r19`). -/
theorem shiftUpdate_threadCertT (τ : String → String) (out : String)
    (h1o : τ (argName 1) ≠ out) :
    ThreadCert τ (([AU, r64] : Ctxt jasminDialect).length + 2) shiftS out
      (straightOpsMem (([AU, r64] : Ctxt jasminDialect).length + 2) shiftUpdate
        (([AU, r64] : Ctxt jasminDialect).length + 2))
      (([AU, r64] : Ctxt jasminDialect).length + 2)
      (accRegMN [AU, r64]) (loopBodyRetArrMN shiftUpdate) := by
  rw [shiftStraight_eq, show loopBodyRetArrMN shiftUpdate = regName 19 by kernel_rfl]
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 4 (resA 3 4 (by omega)) (resA 2 4 (by omega))
  · exact threadArr_acc out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 5 (resA 1 5 (by omega)) (resA 2 5 (by omega))
  · exact threadArr_inv out τ 1 h1o
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_nil 6
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 7 (resR 6 7 (by omega) (by omega)) (resA 0 7 (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_one _ 8 (resR 7 8 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 9 (resR 5 9 (by omega) (by omega)) (resA 0 9 (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_one _ 10 (resR 9 10 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 11 (resR 5 11 (by omega) (by omega)) (resR 8 11 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_one _ 12 (resR 11 12 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 13 (resR 10 13 (by omega) (by omega)) (resR 4 13 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_one _ 14 (resR 13 14 (by omega) (by omega))
  · exact threadArr_none out τ
  refine ⟨?_, ?_, Or.inr ⟨rfl, Or.inl rfl, ?_⟩⟩
  · exact res_three _ _ _ 15 (resA 3 15 (by omega)) (resA 2 15 (by omega))
      (resR 14 15 (by omega) (by omega))
  · exact threadArr_acc out τ
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_nil 16
  · exact thrNone _ τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_two _ _ 17 (resA 2 17 (by omega)) (resR 16 17 (by omega) (by omega))
  · exact thrNone _ τ out
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl, by simp [shiftS], ?_⟩⟩
  · exact res_one _ 18 (resR 17 18 (by omega) (by omega))
  · exact thrNone _ τ out
  refine ⟨?_, ?_, Or.inr ⟨rfl, Or.inr rfl, rfl⟩⟩
  · exact res_three _ _ _ 19 (resR 15 19 (by omega) (by omega))
      (resR 18 19 (by omega) (by omega)) (resR 12 19 (by omega) (by omega))
  · exact thrHead _ τ out


theorem shiftTau_a1 : shiftTau (argName 1) = argName 1 := by
  rw [shiftTau_arg, logicTau_argName_lt 4 19 "a3" (by decide)]

theorem shiftTau_a0 : shiftTau (argName 0) = argName 0 := by
  rw [shiftTau_arg, logicTau_argName_lt 4 19 "a3" (by decide)]

/-- **The canonicalised shipped shift node computes the model loop.** -/
theorem shift_canon_machine_denote (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < ([AU, r64] : Ctxt jasminDialect).length ∧ r = shiftTau (argName j))
    (invs : Ctxt.Valuation ([AU, r64] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx 4)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin NRS → BitVec 64)
    (hseed : StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2)
      (pullM shiftTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AU, r64] : Ctxt jasminDialect).length →
      (b0.reg.getW (shiftTau (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (canonNodeRM shiftTau 4 "a3" c shiftUpdate absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base "a3" 64 NRS
            = some (JLoopBodyN.denote ⟨m, shiftUpdate⟩ invs arr0) :=
  canonNodeRM_faithful shiftUpdate shiftUpdate_arrMemN shiftCanonRen
    (shiftUpdate_threadCertT shiftTau "a3" (by rw [shiftTau_a1]; decide)) absent regs hregs invs
    fn c hc b0 zf hpc arr0 hseed hinv m hm64 hcnt


/-! ## 3. The variable-count shifts -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

theorem min_shiftMask (k : Nat) : min 64 (shiftMask 64 k) = shiftMask 64 k := by
  simp only [shiftMask, ite_true]
  omega

/-- The machine `shlx %d, %d, %c` as a two-address step. -/
def shlxMk (D : String) : JOperand → JInstr 64
  | .reg S => .shlx D D S
  | _ => .shlx D D D

/-- The machine `shrx %d, %d, %c` as a two-address step. -/
def shrxMk (D : String) : JOperand → JInstr 64
  | .reg S => .shrx D D S
  | _ => .shrx D D D

theorem stripWidthTag_SHR64 : stripWidthTag "SHR:64" = "SHR" := by decide +kernel

variable {π : String → String} {L : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}

/-- `SHL:64 d, a, c` against `mov %a, %d; shlx %c, %d, %d`. -/
theorem decSim_shlx_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "SHL:64" d a c] [.mov D (.reg A), .shlx D D C] :=
  decSim_binReg_mov_r (Lay := Lay) (frame := frame) (K := K) (zl := zl) _ "SHL"
    MpnAndBytesValue.stripWidthTag_SHL64 (by decide +kernel) (by decide) (by decide)
    (fun x y => x <<< shiftMask 64 y.toNat) (fun _ _ => rfl) shlxMk
    (fun sa D S r => by
      show (if r = D then x86_SHLX (sa.regs D) (sa.regs S) else sa.regs r) = _
      simp only [x86_SHLX, wshl, shiftCount, min_shiftMask])
    (fun _ _ _ => rfl) d a c D A C hD hA hC hCD ha hc

/-- `SHR:64 d, a, c` against `mov %a, %d; shrx %c, %d, %d`. -/
theorem decSim_shrx_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "SHR:64" d a c] [.mov D (.reg A), .shrx D D C] :=
  decSim_binReg_mov_r (Lay := Lay) (frame := frame) (K := K) (zl := zl) _ "SHR"
    stripWidthTag_SHR64 (by decide +kernel) (by decide) (by decide)
    (fun x y => x >>> shiftMask 64 y.toNat) (fun _ _ => rfl) shrxMk
    (fun sa D S r => by
      show (if r = D then x86_SHRX (sa.regs D) (sa.regs S) else sa.regs r) = _
      simp only [x86_SHRX, wshr, shiftCount, min_shiftMask])
    (fun _ _ _ => rfl) d a c D A C hD hA hC hCD ha hc


/-- The extra step lemmas of this module for `decsim_chain`. -/
macro_rules
  | `(tactic| decsim_step) =>
    `(tactic| focus first
      | (with_reducible apply MpnAndBytesValue.decSim_shlImm0_r; decsim_close)
      | (with_reducible apply decSim_shlx_mov; decsim_close)
      | (with_reducible apply decSim_shrx_mov; decsim_close))

/-! ## 4. The canonicalised node as literals -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
  (shlImm0I andSeeds_eq andSeeds_isLopn loopCtr_four)

/-- The looped segment of the canonicalised shift node, as a literal. -/
def shiftLoopBodyLit : List LinstrRM :=
  [ (.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a3" "Lidx4" 8], .load 64 9)
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)
  , movII "L4_r6" 64
  , binRegI "SUB:64" "L4_r7" "L4_r6" "a0"
  , shlImm0I "L4_r8" "L4_r7"
  , binRegI "SHL:64" "L4_r9" "L4_r5" "a0"
  , shlImm0I "L4_r10" "L4_r9"
  , binRegI "SHR:64" "L4_r11" "L4_r5" "L4_r8"
  , shlImm0I "L4_r12" "L4_r11"
  , binRegI "ADD:64" "L4_r13" "L4_r10" "L4_r4"
  , shlImm0I "L4_r14" "L4_r13"
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "Lidx4" 8, .reg "L4_r14"], .store 64 9)
  , movII "L4_r16" 1
  , binRegI "ADD:64" "L4_r17" "Lidx4" "L4_r16"
  , shlImm0I "L4_r18" "L4_r17"
  , (.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r18" 8, .reg "L4_r12"], .store 64 9)
  , movRI "a3" "a3"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a1")
  , cmpRI "Lctr4" (.reg "a0") ]

theorem shiftStraightRen_eq :
    (straightOpsMem (([AU, r64] : Ctxt jasminDialect).length + 2) shiftUpdate
        (([AU, r64] : Ctxt jasminDialect).length + 2)).map (renRM shiftTau) =
      shiftLoopBodyLit.take 16 := by
  rw [shiftStraight_eq]
  simp only [renRM, renLinstrR, List.map, renOperand, shiftTau_r15, shiftTau_r19,
    shiftTau_arg, logicTau_argName2, logicTau_argName3,
    shiftTau_reg (k := 4) (by decide) (by decide), shiftTau_reg (k := 5) (by decide) (by decide),
    shiftTau_reg (k := 6) (by decide) (by decide), shiftTau_reg (k := 7) (by decide) (by decide),
    shiftTau_reg (k := 8) (by decide) (by decide), shiftTau_reg (k := 9) (by decide) (by decide),
    shiftTau_reg (k := 10) (by decide) (by decide),
    shiftTau_reg (k := 11) (by decide) (by decide),
    shiftTau_reg (k := 12) (by decide) (by decide),
    shiftTau_reg (k := 13) (by decide) (by decide),
    shiftTau_reg (k := 14) (by decide) (by decide),
    shiftTau_reg (k := 16) (by decide) (by decide),
    shiftTau_reg (k := 17) (by decide) (by decide),
    shiftTau_reg (k := 18) (by decide) (by decide)]
  kernel_rfl

theorem shiftCanonBody_eq :
    canonBodyRM shiftTau 4 "a3" shiftUpdate false ["a1", "a0"] = shiftLoopBodyLit := by
  show (straightOpsMem (([AU, r64] : Ctxt jasminDialect).length + 2) shiftUpdate
        (([AU, r64] : Ctxt jasminDialect).length + 2)).map (renRM shiftTau) ++ _ = _
  rw [shiftStraightRen_eq]
  kernel_rfl

theorem shiftNode_eq :
    canonNodeRM shiftTau 4 "a3" "a2" shiftUpdate false ["a1", "a0"]
      = [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" shiftLoopBodyLit := by
  unfold canonNodeRM
  rw [andSeeds_eq, shiftCanonBody_eq, loopCtr_four]

theorem shiftLoopBody_isLopn : ∀ i ∈ shiftLoopBodyLit, IsLopn i := by
  intro i hi
  simp only [shiftLoopBodyLit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

theorem shiftNode_top :
    findLabelMem 4 ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" shiftLoopBodyLit)
      = some (3 + 2) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_top]
  simp

theorem shiftNode_end :
    findLabelMem (4 + 0x40000000) ([movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
        ++ guardedFlagLoopLinstrRM 4 (4 + 0x40000000) "Lctr4" shiftLoopBodyLit)
      = some (3 + shiftLoopBodyLit.length + 5) := by
  rw [MpnMul1DecodedNode.findLabelMem_append_of_isLopn _ _ _ andSeeds_isLopn,
    findLabelMem_guarded_endL _ _ _ _ shiftLoopBody_isLopn (by decide)]
  simp only [Option.map_some, Option.some.injEq, List.length_cons, List.length_nil]
  omega


/-! ## 5. The layout and the relation along the trip -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRtExportTerm
  (shiftDecPre shiftDecLoop shiftDecLoopBody shiftDecPost)

/-- The register assignment of the shift loop node. -/
def shiftPi (r : String) : String :=
  if r = "a3" then "%rbx" else if r = "a1" then "%rcx" else if r = "a0" then "%rsi"
  else if r = "a2" then "%rdx" else if r = "Lidx4" then "%rax" else if r = "Lctr4" then "%rdi"
  else if r = "L4_r4" then "%rdx" else if r = "L4_r5" then "%rbp" else if r = "L4_r6" then "%r8"
  else if r = "L4_r7" then "%r9" else if r = "L4_r8" then "%r8" else if r = "L4_r9" then "%r9"
  else if r = "L4_r10" then "%r10" else if r = "L4_r11" then "%r9"
  else if r = "L4_r12" then "%rbp" else if r = "L4_r13" then "%r8"
  else if r = "L4_r14" then "%rdx" else if r = "L4_r16" then "%rdx"
  else if r = "L4_r17" then "%r8" else if r = "L4_r18" then "%rdx" else r

/-- The array layout: the output `a3` at `rp` with `9` words and slot `s0`, the source `a1`
    at `up` with `8` words and slot `s1`. -/
def shiftLay (rp up : BitVec 64) : Layout where
  base A := if A = "a1" then up else rp
  len A := if A = "a1" then 8 else 9
  slot A := if A = "a3" then some "s0" else if A = "a1" then some "s1" else none

/-- The frame: `s0` at `56(%rsp)`, `s1` at `48(%rsp)`. -/
def shiftFrame (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  if q = "s0" then some (rsp + BitVec.ofInt 64 56)
  else if q = "s1" then some (rsp + BitVec.ofInt 64 48) else none

/-- The cells: the nine words of `a3` and the eight of `a1`. -/
def shiftK (A : String) (j : Nat) : Prop := (A = "a3" ∧ j < 9) ∨ (A = "a1" ∧ j < 8)

/-- The live names at the loop head, after the two loads, before the low store, before the
    high store. -/
abbrev shLive (r : String) : Prop := r ∈ ["a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev shLiveA (r : String) : Prop := r ∈ ["L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev shLiveB (r : String) : Prop :=
  r ∈ ["L4_r5", "L4_r4", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev shLiveC (r : String) : Prop :=
  r ∈ ["L4_r14", "L4_r12", "a3", "a1", "a0", "Lidx4", "Lctr4"]
abbrev shLiveD (r : String) : Prop :=
  r ∈ ["L4_r18", "L4_r12", "a3", "a1", "a0", "Lidx4", "Lctr4"]

/-- The machine registers the trip tracks. -/
def shiftP (rsp : BitVec 64) (x y : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp ∧ sa.regs "%rax" = BitVec.ofNat 64 x ∧ sa.regs "%rdi" = BitVec.ofNat 64 y

theorem shiftP_runBlock (rsp : BitVec 64) (x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rdi"], R ∉ dsts j) (sa : AState)
    (hp : shiftP rsp x y sa) : shiftP rsp x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨by rw [e _ (by simp)]; exact hp.1, by rw [e _ (by simp)]; exact hp.2.1,
    by rw [e _ (by simp)]; exact hp.2.2⟩

def shiftQ (rsp : BitVec 64) (m t : Nat) (sa : AState) : Prop :=
  shiftP rsp (t + 1) (m - (t + 1)) sa
    ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 (m - (t + 1)) == 0#64)

section Trip

variable (rp up rsp : BitVec 64)

abbrev shiftRel (L : String → Prop) (K : String → Nat → Prop) (zl : Prop) (P : AState → Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr shiftPi L (shiftLay rp up) (shiftFrame rsp) K zl sa b zf ∧ P sa

/-- The load of `a3[Lidx4]` through the pointer reloaded from `56(%rsp)`. -/
theorem shift_seg_load3 (t y : Nat) (ht : t < 9) (zl : Prop) :
    DecSim (shiftRel rp up rsp shLive shiftK zl (shiftP rsp t y))
      (shiftRel rp up rsp shLiveA shiftK zl (shiftP rsp t y))
      [(.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a3" "Lidx4" 8], .load 64 9)]
      [.loadMem "%r14" "%rsp" 56, .loadMemIdx "%rdx" "%r14" "%rax" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := shiftLay rp up) (frame := shiftFrame rsp) (K := shiftK) (zl := zl)
      (π := shiftPi) (L := shLive) (L' := shLiveA)
      "L4_r4" "a3" "Lidx4" "%r14" "%rsp" "s0" 56 rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1]; rfl, Or.inl ⟨rfl, by
      show (sa.regs "%rax").toNat < 9
      rw [hp.2.1, ofNat_toNat_lt t (by omega)]; exact ht⟩⟩)
    (shiftP_runBlock rsp t y _ (by decide +kernel))

/-- The load of `a1[Lidx4]` through the pointer reloaded from `48(%rsp)`. -/
theorem shift_seg_load1 (t y : Nat) (ht : t < 8) (zl : Prop) :
    DecSim (shiftRel rp up rsp shLiveA shiftK zl (shiftP rsp t y))
      (shiftRel rp up rsp shLiveB shiftK zl (shiftP rsp t y))
      [(.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)]
      [.loadMem "%r14" "%rsp" 48, .loadMemIdx "%rbp" "%r14" "%rax" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := shiftLay rp up) (frame := shiftFrame rsp) (K := shiftK) (zl := zl)
      (π := shiftPi) (L := shLiveA) (L' := shLiveB)
      "L4_r5" "a1" "Lidx4" "%r14" "%rsp" "s1" 48 rfl (by decide +kernel) (by decide +kernel)
      (by unfold Survives; decide +kernel))
    (fun sa hp => ⟨by rw [hp.1]; rfl, Or.inr ⟨rfl, by
      show (sa.regs "%rax").toNat < 8
      rw [hp.2.1, ofNat_toNat_lt t (by omega)]; exact ht⟩⟩)
    (shiftP_runBlock rsp t y _ (by decide +kernel))

/-- The funnel: the complement count, the two shifted halves and their sum. -/
theorem shift_seg_funnel (t y : Nat) (zl : Prop) :
    DecSim (shiftRel rp up rsp shLiveB shiftK zl (shiftP rsp t y))
      (shiftRel rp up rsp shLiveC shiftK False (shiftP rsp t y))
      (shiftLoopBodyLit.drop 2 |>.take 9)
      [ .mov "%r8" (.imm 64), .mov "%r9" (.reg "%r8"), .sub "%r9" (.reg "%rsi")
      , .mov "%r8" (.reg "%r9"), .mov "%r9" (.reg "%rbp"), .shlx "%r9" "%r9" "%rsi"
      , .mov "%r10" (.reg "%r9"), .mov "%r9" (.reg "%rbp"), .shrx "%r9" "%r9" "%r8"
      , .mov "%rbp" (.reg "%r9"), .mov "%r8" (.reg "%r10"), .add "%r8" (.reg "%rdx")
      , .mov "%rdx" (.reg "%r8") ] := by
  refine DecSim.frame _ _ ?_ (shiftP_runBlock rsp t y _ (by decide +kernel))
  simp only [shiftLoopBodyLit, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero]
  decsim_chain
  exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)

/-- Two distinct words of `a3` below its length lie at distinct addresses. -/
theorem shift_addr_a3_ne {j j' : Nat} (hj : j < 9) (hj' : j' < 9) (hne : j' ≠ j) :
    (shiftLay rp up).addr "a3" j' ≠ (shiftLay rp up).addr "a3" j := by
  intro h
  have h' := congrArg BitVec.toNat (add_left_cancel h)
  simp only [BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

/-- The output words are disjoint from the source words. -/
def shiftDis : Prop :=
  ∀ j j', j < 9 → j' < 8 →
    Disjoint8 ((shiftLay rp up).addr "a3" j) ((shiftLay rp up).addr "a1" j')

theorem shiftK_afterStore (hdis : shiftDis rp up) (j : Nat) (hj : j < 9) :
    ∀ A j', shiftK A j' → afterStore (shiftLay rp up) shiftK "a3" "a3" j A j' := by
  rintro A j' (⟨rfl, hj'⟩ | ⟨rfl, hj'⟩)
  · by_cases hjj : j' = j
    · exact Or.inl ⟨rfl, Or.inl hjj⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨Or.inl ⟨rfl, hj'⟩, shift_addr_a3_ne rp up hj hj' hjj⟩⟩
  · exact Or.inr ⟨by decide, Or.inr ⟨rfl, hj'⟩, ne_of_disjoint8 (hdis j j' hj hj')⟩

/-- The store of the low word to `a3[Lidx4]`. -/
theorem shift_seg_store0 (t y : Nat) (ht : t < 9)
    (hsep : (shiftLay rp up).Sep (shiftFrame rsp)) (hdis : shiftDis rp up) :
    DecSim (shiftRel rp up rsp shLiveC shiftK False (shiftP rsp t y))
      (shiftRel rp up rsp shLiveC shiftK False (shiftP rsp t y))
      [(.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "Lidx4" 8, .reg "L4_r14"], .store 64 9)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rax" 8 (.reg "%rdx")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ _
      (decSim_storeR (π := shiftPi) (L := shLiveC) (Lay := shiftLay rp up)
        (frame := shiftFrame rsp) (K := shiftK) (zl := False) hsep
        "a3" "a3" "Lidx4" "L4_r14" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel) (by decide +kernel) t)
      (fun sa hp => ⟨by rw [hp.1]; rfl, by
        show (sa.regs "%rax").toNat = t
        rw [hp.2.1, ofNat_toNat_lt t (by omega)], Or.inl ⟨rfl, ht⟩⟩)
      (shiftP_runBlock rsp t y _ (by decide +kernel)))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (shiftK_afterStore rp up hdis t ht), h.2⟩)

/-- The high index `Lidx4 + 1`, in `%rdx`. -/
theorem shift_seg_idx1 (t y : Nat) :
    DecSim (shiftRel rp up rsp shLiveC shiftK False (shiftP rsp t y))
      (shiftRel rp up rsp shLiveD shiftK False
        (fun sa => shiftP rsp t y sa ∧ sa.regs "%rdx" = BitVec.ofNat 64 (t + 1)))
      [movII "L4_r16" 1, binRegI "ADD:64" "L4_r17" "Lidx4" "L4_r16",
        shlImm0I "L4_r18" "L4_r17"]
      [.mov "%rdx" (.imm 1), .mov "%r8" (.reg "%rax"), .add "%r8" (.reg "%rdx"),
        .mov "%rdx" (.reg "%r8")] := by
  refine DecSim.frame _ _ ?_ (fun sa hp =>
    ⟨shiftP_runBlock rsp t y _ (by decide +kernel) sa hp, ?_⟩)
  · decsim_chain
    exact fun _ _ _ h => h.mono (by decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.mov X (.imm n))).regs x
        = if x = X then BitVec.ofNat 64 n else s.regs x := fun _ _ _ _ => rfl
    have ea : ∀ (s : AState) (X Y x : String), (evalInstrA s (.add X (.reg Y))).regs x
        = if x = X then s.regs X + s.regs Y else s.regs x := fun _ _ _ _ => rfl
    show (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa (.mov "%rdx" (.imm 1)))
      (.mov "%r8" (.reg "%rax"))) (.add "%r8" (.reg "%rdx"))) (.mov "%rdx" (.reg "%r8"))).regs
      "%rdx" = _
    simp (config := { decide := true }) only [em, ei, ea, ite_true, ite_false]
    rw [hp.2.1]
    exact (BitVec.ofNat_add t 1).symm

/-- The store of the high word to `a3[Lidx4 + 1]`. -/
theorem shift_seg_store1 (t y : Nat) (ht : t + 1 < 9)
    (hsep : (shiftLay rp up).Sep (shiftFrame rsp)) (hdis : shiftDis rp up) :
    DecSim (shiftRel rp up rsp shLiveD shiftK False
        (fun sa => shiftP rsp t y sa ∧ sa.regs "%rdx" = BitVec.ofNat 64 (t + 1)))
      (shiftRel rp up rsp shLiveD shiftK False (shiftP rsp t y))
      [(.Lopn [.reg "a3"] "STOREIDX" [.arrIdx "a3" "L4_r18" 8, .reg "L4_r12"], .store 64 9)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rdx" 8 (.reg "%rbp")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ (shiftP rsp t y)
      (decSim_storeR (π := shiftPi) (L := shLiveD) (Lay := shiftLay rp up)
        (frame := shiftFrame rsp) (K := shiftK) (zl := False) hsep
        "a3" "a3" "L4_r18" "L4_r12" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (t + 1))
      (fun sa hp => ⟨by rw [hp.1.1]; rfl, by
        show (sa.regs "%rdx").toNat = t + 1
        rw [hp.2, ofNat_toNat_lt (t + 1) (by omega)], Or.inl ⟨rfl, ht⟩⟩)
      (fun sa hp => shiftP_runBlock rsp t y _ (by decide +kernel) sa hp.1))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (shiftK_afterStore rp up hdis (t + 1) ht), h.2⟩)

/-- The feedback copy, the index advance, the counter decrement and the three compares. -/
theorem shift_seg_tail (m t : Nat) (htm : t < m) :
    DecSim (shiftRel rp up rsp shLiveD shiftK False (shiftP rsp t (m - t)))
      (shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t))
      [movRI "a3" "a3", addImmI "Lidx4" "Lidx4" 1, subImmI "Lctr4" "Lctr4" 1,
        cmpRI "Lctr4" (.reg "a1"), cmpRI "Lctr4" (.reg "a0"), cmpRI "Lctr4" (.imm 0)]
      [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rdi" (.imm 1),
        .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0)] := by
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
        .sub "%rdi" (.imm 1), .cmp "%rdi" (.reg "%rcx"), .cmp "%rdi" (.reg "%rsi"),
        .cmp "%rdi" (.imm 0)]
      = evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
        (.mov "%rbx" (.reg "%rbx"))) (.add "%rax" (.imm 1))) (.sub "%rdi" (.imm 1)))
        (.cmp "%rdi" (.reg "%rcx"))) (.cmp "%rdi" (.reg "%rsi"))) (.cmp "%rdi" (.imm 0))
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

/-- **One trip of the shipped `mpn_shift_rt` loop**, for each trip `t < m ≤ 8`. -/
theorem shift_trip (m : Nat) (hm : m ≤ 8) (hsep : (shiftLay rp up).Sep (shiftFrame rsp))
    (hdis : shiftDis rp up) (t : Nat) (ht : t < m) :
    DecSim (shiftRel rp up rsp shLive shiftK False (shiftP rsp t (m - t)))
      (shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t))
      (shiftLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
      (shiftDecLoopBody ++ [.cmp "%rdi" (.imm 0)]) :=
  (shift_seg_load3 rp up rsp t (m - t) (by omega) False).append <|
  (shift_seg_load1 rp up rsp t (m - t) (by omega) False).append <|
  (shift_seg_funnel rp up rsp t (m - t) False).append <|
  (shift_seg_store0 rp up rsp t (m - t) (by omega) hsep hdis).append <|
  (shift_seg_idx1 rp up rsp t (m - t)).append <|
  (shift_seg_store1 rp up rsp t (m - t) (by omega) hsep hdis).append <|
  shift_seg_tail rp up rsp m t ht

def shiftG (m : Nat) : AState → LstateM → Bool → Prop :=
  shiftRel rp up rsp shLive shiftK True
    (fun sa => shiftP rsp 0 m sa ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 m == 0#64))

theorem shift_guard (m : Nat) (zl : Prop) :
    DecSim (shiftRel rp up rsp shLive shiftK zl (shiftP rsp 0 m)) (shiftG rp up rsp m)
      [cmpRI "Lctr4" (.imm 0)] [.cmp "%rdi" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ⟨hp, ?_⟩)
  · exact decSim_cmpImm_r "Lctr4" "%rdi" 0 rfl (by decide +kernel)
  · show ZF_of_word (sa.regs "%rdi" - BitVec.ofNat 64 0) = _
    rw [hp.2.2, ZF_of_word_sub]

theorem shift_guard_flag (m : Nat) (hm : m ≤ 8) :
    ∀ sa b zf, shiftG rp up rsp m sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0) := by
  intro sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz]
  exact ofNat_beq_zero_iff m (by omega)

theorem shift_guard_inv (m : Nat) :
    ∀ sa b zf pc, shiftG rp up rsp m sa b zf →
      shiftRel rp up rsp shLive shiftK False (shiftP rsp 0 (m - 0)) sa (b.setLpc pc) zf :=
  fun _ _ _ pc ⟨h, hp, _⟩ => ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

theorem shift_trip_flag (m : Nat) (hm : m ≤ 8) :
    ∀ t, t < m → ∀ sa b zf, shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t) sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m) := by
  intro t ht sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz, ofNat_beq_zero_iff _ (by omega)]
  omega

theorem shift_trip_next (m : Nat) :
    ∀ t, t < m → ∀ sa b zf pc, shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t) sa b zf →
      shiftRel rp up rsp shLive shiftK False (shiftP rsp (t + 1) (m - (t + 1))) sa
        (b.setLpc pc) zf :=
  fun _ _ _ _ _ pc ⟨h, hp, _⟩ =>
    ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

end Trip


/-! ## 6. The prologue and the epilogue -/

/-- The register map at the entry: `rp` (`a3`) in `%rdi`, `up` (`a1`) in `%rsi`, the count
    (`a2`) in `%rdx`, the shift amount (`a0`) in `%rcx`. -/
def shiftPi0 (r : String) : String :=
  if r = "a3" then "%rdi" else if r = "a1" then "%rsi" else if r = "a2" then "%rdx"
  else if r = "a0" then "%rcx" else r

abbrev shiftArgs (r : String) : Prop := r ∈ ["a3", "a1", "a0", "a2"]

def shiftLay0 (rp up : BitVec 64) : Layout := { shiftLay rp up with slot := fun _ => none }

/-- The machine state at the entry. -/
def shiftEntry (rp up rsp : BitVec 64) (m : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp + BitVec.ofInt 64 64 ∧ sa.regs "%rdi" = rp ∧ sa.regs "%rsi" = up
    ∧ sa.regs "%rdx" = BitVec.ofNat 64 m

def shiftStackSep (rp up rsp : BitVec 64) : Prop :=
  ∀ A j, shiftK A j → ∀ o : Int, -16 ≤ o → o ≤ 56 →
    Disjoint8 (rsp + BitVec.ofInt 64 o) ((shiftLay rp up).addr A j)

theorem shiftDecPre_eq : shiftDecPre = MpnAndBytesValue.andPre15 ++
    [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rdx")] := rfl

section Pre

variable (rp up rsp : BitVec 64)

theorem shift_pre15 (m : Nat) (zl : Prop) (hstk : shiftStackSep rp up rsp) :
    DecSim (fun sa b zf => DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK
        zl sa b zf ∧ shiftEntry rp up rsp m sa)
      (shiftRel rp up rsp shiftArgs shiftK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rdx" = BitVec.ofNat 64 m))
      [] MpnAndBytesValue.andPre15 := by
  refine DecSim.machBlock fun sa b zf ⟨h, hrsp, hrdi, hrsi, hrdx⟩ => ?_
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
  simp only [MpnAndBytesValue.andPre15, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  generalize hs' : evalInstrA _ (.loadMem "%rsi" "%rsp" (-16)) = s'
  have hmem := congrArg AState.mem hs'
  have hregs := fun x => congrArg (fun s => AState.regs s x) hs'
  simp (config := { decide := true }) only [em, emm, es, esm, elm, ele, elem,
    evalInstrA_loadMem_regs', ite_true, ite_false, hlea] at hmem hregs
  simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
    [read64_write64_same, read64_write64_of_disjoint] at hregs
  generalize hM : write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64
    (write64 (write64 sa.mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _ = M at hmem
  have hcell : ∀ A j, shiftK A j → read64 M ((shiftLay rp up).addr A j)
      = read64 sa.mem ((shiftLay rp up).addr A j) := by
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
  have hs1 : read64 M (rsp + BitVec.ofInt 64 48) = up := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrsi
  have hr : ∀ x, s'.regs x = _ := fun x => (hregs x).symm
  refine ⟨⟨fun r hr' => ?_, fun hz => hz.elim, fun A j hk => ?_, fun A q hq => ?_⟩, ?_, ?_⟩
  · simp only [shiftArgs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · show _ = some (s'.regs "%rbx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a3" (by decide)
    · show _ = some (s'.regs "%rcx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a1" (by decide)
    · show _ = some (s'.regs "%rsi")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a0" (by decide)
    · show _ = some (s'.regs "%rdx")
      rw [hr]; simp (config := { decide := true }) only [ite_false]
      exact h.regs "a2" (by decide)
  · obtain ⟨hj, arr, ha, hc⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [← hmem, hcell A j hk]; exact hc⟩
  · simp only [shiftLay] at hq
    split_ifs at hq with h0 h1
    · subst h0; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs0]; rfl⟩
    · subst h1; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs1]; rfl⟩
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
  · rw [hr]; simp (config := { decide := true }) only [ite_false]; exact hrdx

theorem shift_seg_seeds (m : Nat) :
    DecSim (shiftRel rp up rsp shiftArgs shiftK False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rdx" = BitVec.ofNat 64 m))
      (shiftRel rp up rsp shLive shiftK False (shiftP rsp 0 m))
      [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
      [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rdi" (.reg "%rdx")] := by
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

theorem shift_pre (m : Nat) (zl : Prop) (hstk : shiftStackSep rp up rsp) :
    DecSim (fun sa b zf => DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK
        zl sa b zf ∧ shiftEntry rp up rsp m sa)
      (shiftRel rp up rsp shLive shiftK False (shiftP rsp 0 m))
      [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"] shiftDecPre := by
  rw [shiftDecPre_eq]
  exact (shift_pre15 rp up rsp m zl hstk).append (shift_seg_seeds rp up rsp m)

/-- The exit relation: the words of the flag machine's `a3` at the output addresses. -/
def shiftOut (sa : AState) (b : LstateM) : Prop :=
  ∃ arr : Fin 9 → BitVec 64, decodeArrM b "a3" 64 9 = some arr
    ∧ ∀ j, j < 9 → read64 sa.mem ((shiftLay rp up).addr "a3" j) = stackGet arr j

theorem shift_post (m : Nat) :
    ∀ sa b, shiftRel rp up rsp shLive shiftK False (shiftP rsp m (m - m)) sa b true →
      shiftOut rp up (aMachine.runBlock sa shiftDecPost) b := by
  intro sa b ⟨h, _⟩
  have hmem : (aMachine.runBlock sa shiftDecPost).mem = sa.mem := rfl
  obtain ⟨_, arr, ha, _⟩ := h.cells "a3" 0 (Or.inl ⟨rfl, by decide⟩)
  refine ⟨arr, ha, fun j hj => ?_⟩
  obtain ⟨_, arr', ha', hr⟩ := h.cells "a3" j (Or.inl ⟨rfl, hj⟩)
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  rw [hmem]; exact hr

end Pre


/-! ## 7. The node, the fold and the result -/

def shiftFuel (n : Nat) : Nat := nodeFuel 3 21 n

/-- **The shipped `mpn_shift_rt` node on both machines, with its fuel.** -/
theorem shift_node_halts_fuel (rp up rsp : BitVec 64) (m : Nat) (hm : m ≤ 8)
    (hsep : (shiftLay rp up).Sep (shiftFrame rsp)) (hdis : shiftDis rp up)
    (hstk : shiftStackSep rp up rsp)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK False sa b zf
      ∧ shiftEntry rp up rsp m sa) :
    ∃ sa' t, Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 sa sa'
      ∧ (∀ k, shiftFuel m ≤ k →
          lsemFuelMemF (singletonProgM fn
            (canonNodeRM shiftTau 4 "a3" "a2" shiftUpdate false ["a1", "a0"])) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ shiftOut rp up sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (shiftRel rp up rsp shLive shiftK False (shiftP rsp t (m - t)))
        (shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t))
        (shiftLoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)])
        (shiftDecLoop.body ++ [shiftDecLoop.cmpInstr]) := by
    intro t ht
    exact shift_trip rp up rsp m hm hsep hdis t ht
  have hg : DecSim (shiftRel rp up rsp shLive shiftK False (shiftP rsp 0 m))
      (shiftG rp up rsp m) [cmpRI "Lctr4" (.imm 0)] [shiftDecLoop.cmpInstr] :=
    shift_guard rp up rsp m False
  rw [shiftNode_eq]
  exact decNode_halts_fuel fn [movRI "a3" "a3", movII "Lidx4" 0, movRI "Lctr4" "a2"]
    shiftLoopBodyLit 4 (4 + 0x40000000) "Lctr4" shiftDecLoop m _ _ (shiftG rp up rsp m)
    (fun t => shiftRel rp up rsp shLive shiftK False (shiftP rsp t (m - t)))
    (fun t => shiftRel rp up rsp shLive shiftK True (shiftQ rsp m t)) (shiftOut rp up)
    shiftDecPre shiftDecPost andSeeds_isLopn shiftLoopBody_isLopn shiftNode_top shiftNode_end
    (shift_pre rp up rsp m False hstk) hg (shift_guard_flag rp up rsp m hm)
    (shift_guard_inv rp up rsp m) hsim (shift_trip_flag rp up rsp m hm)
    (shift_trip_next rp up rsp m) (shift_post rp up rsp m) sa b zf hpc hE

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
  (shiftFold shiftFoldStep vmBody shiftBodyLowCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote
  (shiftLimbBody_run shiftEnv consistentS_shiftEnv shiftBody_covered shiftUpdate_eq)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC (frontLoopBodyJ_denote_foldl)

/-- **The front-compiled shift body folds `shiftFoldStep`.** -/
theorem shift_fold_denote (up : Fin NUS → BitVec 64) (sh : BitVec 64)
    (hsh : 0 < sh.toNat ∧ sh.toNat < 64) (acc : Fin NRS → BitVec 64) (n : Nat)
    (hn : n < 2 ^ 64) :
    JLoopBodyN.denote ⟨n, shiftUpdate⟩
        (HVector.cons up (HVector.cons sh HVector.nil) :
          Ctxt.Valuation ([AU, r64] : Ctxt jasminDialect)) acc
      = shiftFold up sh.toNat n acc :=
  frontLoopBodyJ_denote_foldl (accCTy := .memref NRS) (invCTys := [.memref NUS, .sword 64])
    vmBody "rp" shiftBodyLowCT shiftBody_covered (.cons up (.cons sh .nil))
    (fun arr tt => shiftFoldStep up sh.toNat arr tt) n
    (fun tt arr htt => by
      obtain ⟨env', hrun, hrp⟩ := shiftLimbBody_run up sh arr tt hsh (by omega)
      exact ⟨shiftEnv up sh arr (BitVec.ofNat 64 tt), env',
        consistentS_shiftEnv up sh arr (BitVec.ofNat 64 tt), hrun, hrp⟩)
    shiftUpdate_eq acc

/-- **The decoded shipped `mpn_shift_rt` computes the funnel-shift fold.** Under the entry
    correspondence and the seed agreement with the source words `up`, the shift amount `sh`
    (`0 < sh < 64`) and the output seed `arr0`: the machine halts on the decoded layout and
    the nine words at `rp` are those of `shiftFold up sh m arr0`. -/
theorem shift_decoded_val (rp upp rsp : BitVec 64) (m : Nat) (hm : m ≤ 8)
    (hsep : (shiftLay rp upp).Sep (shiftFrame rsp)) (hdis : shiftDis rp upp)
    (hstk : shiftStackSep rp upp rsp)
    (fn : String) (sa : AState) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hE : DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp upp) (fun _ => none) shiftK False sa b0 zf
      ∧ shiftEntry rp upp rsp m sa)
    (up : Fin NUS → BitVec 64) (sh : BitVec 64) (hsh : 0 < sh.toNat ∧ sh.toNat < 64)
    (arr0 : Fin NRS → BitVec 64)
    (hseed : StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2)
      (pullM shiftTau (b0.setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AU, r64] : Ctxt jasminDialect)) (.cons up (.cons sh .nil)) 0
        arr0)) :
    ∃ sa', Halts aMachine (nodeLayout shiftDecPre shiftDecLoop shiftDecPost) 0 sa sa'
      ∧ ∀ j, j < 9 → read64 sa'.mem ((shiftLay rp upp).addr "a3" j)
          = stackGet (shiftFold up sh.toNat m arr0) j := by
  obtain ⟨sa', t1, hh, hrun1, arr, ha, hw⟩ :=
    shift_node_halts_fuel rp upp rsp m hm hsep hdis hstk fn sa b0 zf hpc hE
  have hregs : ∀ r ∈ ["a1", "a0"], ∃ j, j < ([AU, r64] : Ctxt jasminDialect).length ∧
      r = shiftTau (argName j) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨1, by decide, by rw [shiftTau_a1]; rfl⟩
    · exact ⟨0, by decide, by rw [shiftTau_a0]; rfl⟩
  have hinv : ∀ j, j < ([AU, r64] : Ctxt jasminDialect).length →
      (b0.reg.getW (shiftTau (argName j)) 64).isSome := by
    intro j hj
    have hj2 : j = 0 ∨ j = 1 := by
      have : j < 2 := hj
      omega
    rcases hj2 with rfl | rfl
    · rw [shiftTau_a0, show argName 0 = "a0" from rfl, hE.1.regs "a0" (by decide)]; rfl
    · rw [shiftTau_a1, show argName 1 = "a1" from rfl, hE.1.regs "a1" (by decide)]; rfl
  have hcnt : b0.reg.getW "a2" 64 = some (BitVec.ofNat 64 m) := by
    rw [hE.1.regs "a2" (by decide)]
    exact congrArg some hE.2.2.2.2
  obtain ⟨k, t2, hrun2, hdec⟩ := shift_canon_machine_denote false ["a1", "a0"] hregs
    (.cons up (.cons sh .nil)) fn "a2" (by decide +kernel) b0 zf hpc arr0 hseed hinv m
    (by omega) hcnt
  have he : t1 = t2 := lsemFuelMemF_det _ _ _ _ _ _ (hrun1 _ (Nat.le_refl _)) hrun2
  subst he
  have hd : decodeArrM t1.prog.base "a3" 64 9
      = some (JLoopBodyN.denote ⟨m, shiftUpdate⟩ (.cons up (.cons sh .nil)) arr0) := hdec
  rw [ha] at hd
  obtain rfl := Option.some.inj hd
  have key := shift_fold_denote up sh hsh arr0 m (by omega)
  refine ⟨sa', hh, fun j hj => ?_⟩
  rw [hw j hj]
  exact congrArg (fun x => stackGet x j) key


open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)

/-- **`mpn_shift_rt`, from the linked program to its result words.** The program
    `MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt"` that `MpnRuntimeBytesEmit.kernels` maps
    to the linked object is one function `mpn_shift_rt`; its function bytes decode to `prog`;
    and from every entry state with `rp`, `up` and the count `m ≤ 8` in `%rdi`, `%rsi`,
    `%rdx` (the shift amount in `%rcx`), the output words separated from the source words and
    both from the frame, and a corresponding flag-machine state agreeing with the source words
    `up`, the shift amount `sh` with `0 < sh < 64` and the output seed `arr0` whose word `0` is
    below `2 ^ sh`: the machine halts on `prog`, and the `m + 1` words from `rp` hold
    `up[0..m) · 2 ^ sh + arr0[0]`. -/
theorem mpn_shift_rt_bytes_correct :
    ∃ f : Lfundef,
      (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt").map (·.lp_funcs)
        = some [("mpn_shift_rt", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp upp rsp : BitVec 64) (m : Nat), m ≤ 8 →
        (shiftLay rp upp).Sep (shiftFrame rsp) → shiftDis rp upp → shiftStackSep rp upp rsp →
        ∀ (sa : AState) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
        DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp upp) (fun _ => none) shiftK False sa b0 zf →
        shiftEntry rp upp rsp m sa →
        ∀ (up : Fin NUS → BitVec 64) (sh : BitVec 64) (arr0 : Fin NRS → BitVec 64),
        0 < sh.toNat ∧ sh.toNat < 64 → (memGetDyn arr0 0).toNat < 2 ^ sh.toNat →
        StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
          (([AU, r64] : Ctxt jasminDialect).length + 2)
          (pullM shiftTau (b0.setReg (loopIdx 4) (0#64)))
          (tripValArrMN (invTys := ([AU, r64] : Ctxt jasminDialect)) (.cons up (.cons sh .nil)) 0
            arr0) →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ bignumVal ((List.range (m + 1)).map
              (fun j => read64 sa'.mem (rp + BitVec.ofNat 64 (8 * j))))
            = bignumVal (cells up m) * 2 ^ sh.toNat + (memGetDyn arr0 0).toNat := by
  refine ⟨_, by rw [MpnRtExportTerm.shiftLprog_eq]; rfl,
    nodeLayout shiftDecPre shiftDecLoop shiftDecPost, ?_, fun rp upp rsp m hm hsep hdis hstk
    sa b0 zf hpc hE hent up sh arr0 hsh h0 hseed => ?_⟩
  · rw [MpnRtExportTerm.shiftPhysAbi_eq]
    exact MpnRtExportTerm.shiftPhysLit_decode
  · obtain ⟨sa', hh, hw⟩ := shift_decoded_val rp upp rsp m hm hsep hdis hstk
      "mpn_shift_rt" sa b0 zf hpc ⟨hE, hent⟩ up sh hsh arr0 hseed
    refine ⟨sa', hh, ?_⟩
    have hl : (List.range (m + 1)).map (fun j => read64 sa'.mem (rp + BitVec.ofNat 64 (8 * j)))
        = cells (shiftFold up sh.toNat m arr0) (m + 1) := by
      unfold cells
      refine List.map_congr_left (fun j hj => ?_)
      have hj' : j < m + 1 := List.mem_range.mp hj
      rw [show rp + BitVec.ofNat 64 (8 * j) = (shiftLay rp upp).addr "a3" j from rfl,
        hw j (by omega), DialectToJasminComCorrect.stackGet_eq_memGetDyn]
    rw [hl]
    exact MpnShiftFrontEmit.shiftFold_val up sh.toNat (by omega) arr0 h0 m (by show m < 9; omega)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue
