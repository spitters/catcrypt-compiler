/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnXorBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnIorBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesValue

@[expose] public section

set_option autoImplicit false

/-!
# The flag-machine entry of the chain kernels, read off the machine state

The `*_bytes_correct` theorems of `MpnAndBytesValue` and its siblings take a flag-machine
entry state `b0` with two conditions: it corresponds to the machine entry state, and it
agrees with the source valuation. This module builds `b0` from the machine state
(`entryM`: each argument name holds its register, each array name the words at its
register's address) and discharges both conditions, so that the kernel theorems speak of the
machine state alone.

## Main results

* `mpn_and_n_entry_correct`, `mpn_xor_n_entry_correct`, `mpn_ior_n_entry_correct`: from every
  machine entry state of the bitwise kernel with the words separated, the machine halts with the
  limbwise conjunction, exclusive or or inclusive or of the two inputs in `rp`.
* `mpn_shift_rt_entry_correct`: the runtime shift kernel halts with the shifted bignum value of
  the input in `rp`.
* `mpn_cmp_ct_entry_correct`: the constant-time compare kernel halts with the comparison sign of
  the two bignum values in `rp`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
  (tripValArrMN resolveVar_trip_acc resolveVar_trip_idx accRegMN idxRegMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (pullM pullM_getW pullM_getArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)

/-! ## 1. The entry state -/

/-- The `n` words at the address `base` of the memory of `sa`. -/
def wordsAt (sa : AState) (base : BitVec 64) (n : Nat) : Fin n → BitVec 64 :=
  fun i => read64 sa.mem (base + BitVec.ofNat 64 (8 * i.val))

/-- The flag-machine state read off `sa`: the name `r` of `regs` holds its value at width
    `64`, the name `A` of `arrs` with address `p` and length `n` holds the `n` words at `p`;
    every other cell is empty and the program counter is `0`. -/
def entryM (regs : List (String × BitVec 64)) (arrs : List (String × (BitVec 64 × Nat)))
    (sa : AState) : LstateM where
  reg :=
    { lvm := fun r => match regs.lookup r with
        | some v => ⟨64, v⟩
        | none => ⟨0, 0#0⟩
      lpc := 0 }
  larr := fun r => match arrs.lookup r with
    | some (p, n) => ⟨64, n, wordsAt sa p n⟩
    | none => ArrCell.default

variable {regs : List (String × BitVec 64)} {arrs : List (String × (BitVec 64 × Nat))}
  {sa : AState}

theorem entryM_lpc : (entryM regs arrs sa).lpc = 0 := rfl

theorem entryM_getW {r : String} {v : BitVec 64} (h : regs.lookup r = some v) :
    (entryM regs arrs sa).reg.getW r 64 = some v := by
  have hl : (entryM regs arrs sa).reg.lvm r = ⟨64, v⟩ := by
    simp only [entryM, h]
  unfold LstateN.getW
  rw [hl]
  simp

theorem entryM_getArr {r : String} {p : BitVec 64} {n : Nat} (h : arrs.lookup r = some (p, n)) :
    (entryM regs arrs sa).getArr r 64 n = some (wordsAt sa p n) := by
  have hl : (entryM regs arrs sa).larr r = ⟨64, n, wordsAt sa p n⟩ := by
    simp only [entryM, h]
  unfold LstateM.getArr
  rw [hl]
  simp

theorem getArr_setReg (s : LstateM) (r x : String) {w : Nat} (v : BitVec w) (w' n : Nat) :
    (s.setReg x v).getArr r w' n = s.getArr r w' n := rfl

theorem stackGet_wordsAt {p : BitVec 64} {n j : Nat} (hj : j < n) :
    stackGet (wordsAt sa p n) j = read64 sa.mem (p + BitVec.ofNat 64 (8 * j)) := by
  cases n with
  | zero => omega
  | succ n => simp [stackGet, wordsAt, Nat.mod_eq_of_lt hj]

theorem memGetDyn_wordsAt {p : BitVec 64} {n j : Nat} (hj : j < n) :
    memGetDyn (wordsAt sa p n) j = read64 sa.mem (p + BitVec.ofNat 64 (8 * j)) := by
  cases n with
  | zero => omega
  | succ n => simp [memGetDyn, wordsAt, Nat.mod_eq_of_lt hj]

/-! ## 2. `mpn_and_n_loop_owned` -/

section And

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue

/-- The entry state of the conjunction: `a3`, `a1`, `a0`, `a2` hold `%rdi`, `%rsi`, `%rdx`,
    `%rcx`, and the arrays `a3`, `a1`, `a0` the four words at `%rdi`, `%rsi`, `%rdx`. -/
def andB0 (sa : AState) : LstateM :=
  entryM [("a3", sa.regs "%rdi"), ("a1", sa.regs "%rsi"), ("a0", sa.regs "%rdx"),
      ("a2", sa.regs "%rcx")]
    [("a3", (sa.regs "%rdi", 4)), ("a1", (sa.regs "%rsi", 4)), ("a0", (sa.regs "%rdx", 4))] sa

theorem andB0_corr (rp ap bp rsp : BitVec 64) (m : Nat) (sa : AState)
    (hE : andEntry rp ap bp rsp m sa) (zf : Bool) :
    DecLsemCorr andPi0 andArgs (andLay0 rp ap bp) (fun _ => none) andK False sa (andB0 sa) zf where
  regs r hr := by
    simp only [andArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact entryM_getW (by simp (config := { decide := true }) [andPi0, List.lookup])
  zfEq h := h.elim
  cells A j hk := by
    obtain ⟨hE0, hE1, hE2, hE3, -⟩ := hE
    obtain ⟨hA, hj⟩ := hk
    rcases hA with rfl | rfl | rfl
    · refine ⟨hj, wordsAt sa (sa.regs "%rdi") 4,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup, andLay0, andLay]), ?_⟩
      show _ = stackGet (wordsAt sa (sa.regs "%rdi") 4) j
      rw [stackGet_wordsAt hj, hE1]
      simp (config := { decide := true }) [Layout.addr, andLay0, andLay]
    · refine ⟨hj, wordsAt sa (sa.regs "%rsi") 4,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup, andLay0, andLay]), ?_⟩
      show _ = stackGet (wordsAt sa (sa.regs "%rsi") 4) j
      rw [stackGet_wordsAt hj, hE2]
      simp (config := { decide := true }) [Layout.addr, andLay0, andLay]
    · refine ⟨hj, wordsAt sa (sa.regs "%rdx") 4,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup, andLay0, andLay]), ?_⟩
      show _ = stackGet (wordsAt sa (sa.regs "%rdx") 4) j
      rw [stackGet_wordsAt hj, hE3]
      simp (config := { decide := true }) [Layout.addr, andLay0, andLay]
  slots A q h := by simp [andLay0] at h

theorem andB0_seed (sl : Nat) (sa : AState) :
    StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (logicTau 4 sl "a3") ((andB0 sa).setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AN, AN] : Ctxt jasminDialect))
        (.cons (wordsAt sa (sa.regs "%rsi") 4) (.cons (wordsAt sa (sa.regs "%rdx") 4) .nil)) 0
        (wordsAt sa (sa.regs "%rdi") 4)) := by
  refine ⟨fun {w'} v => ?_, fun {w' n'} v => ?_⟩
  · cases v with
    | there v' =>
      cases v' with
      | here =>
        rw [resolveVar_trip_idx, evalOperandN, pullM_getW]
        show ((andB0 sa).setReg (loopIdx 4) (0#64)).reg.getW (logicTau 4 sl "a3" (argName 2)) 64 = _
        rw [logicTau_argName2, LstateM.reg_setReg, LstateN.getW_setReg_same]
        rfl
      | there u =>
        cases u with
        | there u' => cases u' with
          | there u'' => cases u''
  · cases v with
    | here =>
      rw [resolveVar_trip_acc]
      simp only [operandName, pullM_getArr]
      show ((andB0 sa).setReg (loopIdx 4) (0#64)).getArr (logicTau 4 sl "a3" (argName 3)) 64 4 = _
      rw [logicTau_argName3, getArr_setReg]
      exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
    | there v' =>
      cases v' with
      | there u =>
        cases u with
        | here =>
          show ((andB0 sa).setReg (loopIdx 4) (0#64)).getArr (logicTau 4 sl "a3" (argName 1)) 64 4 = _
          rw [logicTau_argName_lt 4 sl "a3" (by decide), getArr_setReg,
            show argName 1 = "a1" from rfl]
          exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
        | there u' =>
          cases u' with
          | here =>
            show ((andB0 sa).setReg (loopIdx 4) (0#64)).getArr (logicTau 4 sl "a3" (argName 0)) 64 4 = _
            rw [logicTau_argName_lt 4 sl "a3" (by decide), getArr_setReg,
              show argName 0 = "a0" from rfl]
            exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
          | there u'' => cases u''

/-- The words `j < m` read at `p` from `sa`. -/
abbrev wd (sa : AState) (p : BitVec 64) (j : Nat) : BitVec 64 :=
  read64 sa.mem (p + BitVec.ofNat 64 (8 * j))

/-- **`mpn_and_n_loop_owned` from the machine entry.** The program and its decoded function
    bytes as in `mpn_and_n_bytes_correct`; from every machine state with `rp`, `ap`, `bp`
    and the count `m ≤ 4` in `%rdi`, `%rsi`, `%rdx`, `%rcx` and the stack pointer `64`
    above `rsp`, under the separation hypotheses, the machine halts with
    `ap[j] &&& bp[j]` (the entry words) at `rp + 8 j` for every `j < m`. -/
theorem mpn_and_n_entry_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.andLprog ()).map (·.lp_funcs) = some [("mpn_and_n_loop_owned", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ ∀ j, j < m → wd sa' rp j = wd sa ap j &&& wd sa bp j := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_and_n_bytes_correct
  refine ⟨f, hf, prog, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa', hh, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa (andB0 sa) false entryM_lpc
    (andB0_corr rp ap bp rsp m sa hE false) hE _ _ _ (andB0_seed 9 sa)
  refine ⟨sa', hh, fun j hj => ?_⟩
  show read64 sa'.mem _ = _
  rw [hw j hj, memGetDyn_wordsAt (show j < 4 by omega),
    memGetDyn_wordsAt (show j < 4 by omega), hE.2.2.1, hE.2.2.2.1]

end And

/-! ## 3. `mpn_xor_n_loop_owned` and `mpn_ior_n_loop_owned` -/

section XorIor

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAndBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnXorBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnIorBytesValue

/-- **`mpn_xor_n_loop_owned` from the machine entry**, as `mpn_and_n_entry_correct`. -/
theorem mpn_xor_n_entry_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.xorLprog ()).map (·.lp_funcs) = some [("mpn_xor_n_loop_owned", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ ∀ j, j < m → wd sa' rp j = wd sa ap j ^^^ wd sa bp j := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_xor_n_bytes_correct
  refine ⟨f, hf, prog, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa', hh, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa (andB0 sa) false entryM_lpc
    (andB0_corr rp ap bp rsp m sa hE false) hE _ _ _ (andB0_seed 9 sa)
  refine ⟨sa', hh, fun j hj => ?_⟩
  show read64 sa'.mem _ = _
  rw [hw j hj, memGetDyn_wordsAt (show j < 4 by omega),
    memGetDyn_wordsAt (show j < 4 by omega), hE.2.2.1, hE.2.2.2.1]

/-- **`mpn_ior_n_loop_owned` from the machine entry**, as `mpn_and_n_entry_correct`. -/
theorem mpn_ior_n_entry_correct :
    ∃ f : Lfundef,
      (MpnLoopFrontEmit.iorLprog ()).map (·.lp_funcs) = some [("mpn_ior_n_loop_owned", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp ap bp rsp : BitVec 64) (m : Nat), m ≤ 4 →
        (andLay rp ap bp).Sep (andFrame rsp) → andDis rp ap bp → andStackSep rp ap bp rsp →
        ∀ sa : AState, andEntry rp ap bp rsp m sa →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ ∀ j, j < m → wd sa' rp j = wd sa ap j ||| wd sa bp j := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_ior_n_bytes_correct
  refine ⟨f, hf, prog, hdec, fun rp ap bp rsp m hm hsep hdis hstk sa hE => ?_⟩
  obtain ⟨sa', hh, hw⟩ := H rp ap bp rsp m hm hsep hdis hstk sa (andB0 sa) false entryM_lpc
    (andB0_corr rp ap bp rsp m sa hE false) hE _ _ _ (andB0_seed 11 sa)
  refine ⟨sa', hh, fun j hj => ?_⟩
  show read64 sa'.mem _ = _
  rw [hw j hj, memGetDyn_wordsAt (show j < 4 by omega),
    memGetDyn_wordsAt (show j < 4 by omega), hE.2.2.1, hE.2.2.2.1]

end XorIor

/-! ## 4. `mpn_shift_rt` -/

section Shift

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit (AU r64 NRS NUS)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)

theorem cells_wordsAt {p : BitVec 64} {n m : Nat} (hm : m ≤ n) :
    cells (wordsAt sa p n) m = (List.range m).map (wd sa p) := by
  unfold cells
  refine List.map_congr_left (fun j hj => ?_)
  exact memGetDyn_wordsAt (by have := List.mem_range.mp hj; omega)

/-- The entry state of the shift: `a3`, `a1`, `a0`, `a2` hold `%rdi`, `%rsi`, `%rcx`, `%rdx`;
    the array `a3` the nine words at `%rdi`, `a1` the eight at `%rsi`. -/
def shiftB0 (sa : AState) : LstateM :=
  entryM [("a3", sa.regs "%rdi"), ("a1", sa.regs "%rsi"), ("a0", sa.regs "%rcx"),
      ("a2", sa.regs "%rdx")]
    [("a3", (sa.regs "%rdi", 9)), ("a1", (sa.regs "%rsi", 8))] sa

theorem shiftB0_corr (rp up rsp : BitVec 64) (m : Nat) (sa : AState)
    (hE : shiftEntry rp up rsp m sa) (zf : Bool) :
    DecLsemCorr shiftPi0 shiftArgs (shiftLay0 rp up) (fun _ => none) shiftK False sa
      (shiftB0 sa) zf where
  regs r hr := by
    simp only [shiftArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact entryM_getW (by simp (config := { decide := true }) [shiftPi0, List.lookup])
  zfEq h := h.elim
  cells A j hk := by
    obtain ⟨-, hE1, hE2, -⟩ := hE
    rcases hk with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · have hl : (shiftLay0 rp up).len "a3" = 9 := by
        simp (config := { decide := true }) [shiftLay0, shiftLay]
      rw [hl]
      refine ⟨hj, wordsAt sa (sa.regs "%rdi") 9,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup]), ?_⟩
      rw [stackGet_wordsAt hj, hE1]
      simp (config := { decide := true }) [Layout.addr, shiftLay0, shiftLay]
    · have hl : (shiftLay0 rp up).len "a1" = 8 := by
        simp (config := { decide := true }) [shiftLay0, shiftLay]
      rw [hl]
      refine ⟨hj, wordsAt sa (sa.regs "%rsi") 8,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup]), ?_⟩
      rw [stackGet_wordsAt hj, hE2]
      simp (config := { decide := true }) [Layout.addr, shiftLay0, shiftLay]
  slots A q h := by simp [shiftLay0] at h

theorem shiftTau_argName (k : Nat) : shiftTau (argName k) = logicTau 4 19 "a3" (argName k) :=
  shiftTau_ne15 (argName_ne_r15 k)

theorem shiftB0_seed (sa : AState) :
    StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2)
      (pullM shiftTau ((shiftB0 sa).setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AU, r64] : Ctxt jasminDialect))
        (.cons (wordsAt sa (sa.regs "%rsi") 8) (.cons (sa.regs "%rcx") .nil)) 0
        (wordsAt sa (sa.regs "%rdi") 9)) := by
  refine ⟨fun {w'} v => ?_, fun {w' n'} v => ?_⟩
  · cases v with
    | there v1 =>
      cases v1 with
      | here =>
        rw [resolveVar_trip_idx, evalOperandN, pullM_getW]
        show ((shiftB0 sa).setReg (loopIdx 4) (0#64)).reg.getW (shiftTau (argName 2)) 64 = _
        rw [shiftTau_argName, logicTau_argName2, LstateM.reg_setReg, LstateN.getW_setReg_same]
        rfl
      | there u =>
        cases u with
        | there u1 => cases u1 with
          | here =>
            show ((shiftB0 sa).setReg (loopIdx 4) (0#64)).reg.getW (shiftTau (argName 0)) 64 = _
            rw [shiftTau_argName, logicTau_argName_lt 4 19 "a3" (by decide), LstateM.reg_setReg,
              LstateN.getW_setReg_other _ _ _ _ _ (loopIdx_ne_argName 4 0).symm,
              show argName 0 = "a0" from rfl]
            exact (entryM_getW (v := sa.regs "%rcx")
              (by simp (config := { decide := true }) [List.lookup])).trans rfl
          | there u2 => cases u2
  · cases v with
    | here =>
      rw [resolveVar_trip_acc]
      simp only [operandName, pullM_getArr]
      show ((shiftB0 sa).setReg (loopIdx 4) (0#64)).getArr (shiftTau (argName 3)) 64 9 = _
      rw [shiftTau_argName, logicTau_argName3, getArr_setReg]
      exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
    | there v1 =>
      cases v1 with
      | there u =>
        cases u with
        | here =>
          show ((shiftB0 sa).setReg (loopIdx 4) (0#64)).getArr (shiftTau (argName 1)) 64 8 = _
          rw [shiftTau_argName, logicTau_argName_lt 4 19 "a3" (by decide), getArr_setReg,
            show argName 1 = "a1" from rfl]
          exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
        | there u1 =>
          cases u1 with
          | there u2 => cases u2

/-- **`mpn_shift_rt` from the machine entry.** The program and its decoded function bytes as
    in `mpn_shift_rt_bytes_correct`; from every machine state with `rp`, `up`, the count
    `m ≤ 8` and the shift amount `sh` in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `0 < sh < 64`, and
    the entry word at `rp` below `2 ^ sh` (the carry-in of the model), under the separation
    hypotheses, the machine halts and the `m + 1` words at `rp` are the `m` entry words at
    `up` shifted left by `sh`, plus the carry-in. -/
theorem mpn_shift_rt_entry_correct :
    ∃ f : Lfundef,
      (MpnShiftFrontEmit.shiftRtLprogOpt "mpn_shift_rt").map (·.lp_funcs)
        = some [("mpn_shift_rt", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp upp rsp : BitVec 64) (m : Nat), m ≤ 8 →
        (shiftLay rp upp).Sep (shiftFrame rsp) → shiftDis rp upp → shiftStackSep rp upp rsp →
        ∀ sa : AState, shiftEntry rp upp rsp m sa →
        0 < (sa.regs "%rcx").toNat ∧ (sa.regs "%rcx").toNat < 64 →
        (wd sa rp 0).toNat < 2 ^ (sa.regs "%rcx").toNat →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ bignumVal ((List.range (m + 1)).map (wd sa' rp))
            = bignumVal ((List.range m).map (wd sa upp)) * 2 ^ (sa.regs "%rcx").toNat
              + (wd sa rp 0).toNat := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_shift_rt_bytes_correct
  refine ⟨f, hf, prog, hdec, fun rp upp rsp m hm hsep hdis hstk sa hE hsh h0 => ?_⟩
  have hw0 : memGetDyn (wordsAt sa (sa.regs "%rdi") 9) 0 = wd sa rp 0 := by
    rw [memGetDyn_wordsAt (by decide), hE.2.1]
  obtain ⟨sa', hh, hw⟩ := H rp upp rsp m hm hsep hdis hstk sa (shiftB0 sa) false entryM_lpc
    (shiftB0_corr rp upp rsp m sa hE false) hE _ _ _ hsh (by rw [hw0]; exact h0)
    (shiftB0_seed sa)
  refine ⟨sa', hh, ?_⟩
  rw [hw0, cells_wordsAt (show m ≤ 8 from hm), hE.2.2.1] at hw
  exact hw

end Shift

/-! ## 5. `mpn_cmp_ct` -/

section Cmp

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpBytesValue
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit (AO r64 NR NU cmpSign)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)

theorem segCells_wordsAt {p : BitVec 64} {n m : Nat} (hm : m ≤ n) :
    segCells (wordsAt sa p n) 0 m = (List.range m).map (wd sa p) := by
  unfold segCells
  refine List.map_congr_left (fun j hj => ?_)
  rw [Nat.zero_add]
  exact memGetDyn_wordsAt (by have := List.mem_range.mp hj; omega)

/-- The entry state of the compare: `a4`, `a2`, `a1`, `a0` hold `%rdi`, `%rsi`, `%rdx`,
    `%rcx`; the array `a4` the word at `%rdi`, `a2` and `a1` the eight words at `%rsi` and
    `%rdx`. -/
def cmpB0 (sa : AState) : LstateM :=
  entryM [("a4", sa.regs "%rdi"), ("a2", sa.regs "%rsi"), ("a1", sa.regs "%rdx"),
      ("a0", sa.regs "%rcx")]
    [("a4", (sa.regs "%rdi", 1)), ("a2", (sa.regs "%rsi", 8)), ("a1", (sa.regs "%rdx", 8))] sa

theorem cmpB0_corr (rp ap bp rsp : BitVec 64) (m : Nat) (sa : AState)
    (hE : cmpEntry rp ap bp rsp m sa) (zf : Bool) :
    DecLsemCorr cmpPi0 cmpArgs0 (cmpLay0 rp ap bp) (fun _ => none) cmpK False sa
      (cmpB0 sa) zf where
  regs r hr := by
    simp only [cmpArgs0, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact entryM_getW (by simp (config := { decide := true }) [cmpPi0, List.lookup])
  zfEq h := h.elim
  cells A j hk := by
    obtain ⟨-, hE1, hE2, hE3, -⟩ := hE
    rcases hk with ⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, hj⟩
    · have hl : (cmpLay0 rp ap bp).len "a4" = 1 := by
        simp (config := { decide := true }) [cmpLay0, cmpLay]
      rw [hl]
      refine ⟨hj, wordsAt sa (sa.regs "%rdi") 1,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup]), ?_⟩
      rw [stackGet_wordsAt hj, hE1]
      simp (config := { decide := true }) [Layout.addr, cmpLay0, cmpLay]
    · have hl : (cmpLay0 rp ap bp).len "a2" = 8 := by
        simp (config := { decide := true }) [cmpLay0, cmpLay]
      rw [hl]
      refine ⟨hj, wordsAt sa (sa.regs "%rsi") 8,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup]), ?_⟩
      rw [stackGet_wordsAt hj, hE2]
      simp (config := { decide := true }) [Layout.addr, cmpLay0, cmpLay]
    · have hl : (cmpLay0 rp ap bp).len "a1" = 8 := by
        simp (config := { decide := true }) [cmpLay0, cmpLay]
      rw [hl]
      refine ⟨hj, wordsAt sa (sa.regs "%rdx") 8,
        entryM_getArr (by simp (config := { decide := true }) [List.lookup]), ?_⟩
      rw [stackGet_wordsAt hj, hE3]
      simp (config := { decide := true }) [Layout.addr, cmpLay0, cmpLay]
  slots A q h := by simp [cmpLay0] at h

theorem cmpB0_seed (sa : AState) (m : Nat) (hc : sa.regs "%rcx" = BitVec.ofNat 64 m) :
    StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (pullM cmpTau ((cmpB0 sa).setReg (loopIdx 4) (0#64)))
      (tripValArrMN (invTys := ([AO, AO, r64] : Ctxt jasminDialect))
        (.cons (wordsAt sa (sa.regs "%rsi") 8) (.cons (wordsAt sa (sa.regs "%rdx") 8)
          (.cons (BitVec.ofNat 64 m) .nil))) 0
        (wordsAt sa (sa.regs "%rdi") 1)) := by
  refine ⟨fun {w'} v => ?_, fun {w' n'} v => ?_⟩
  · cases v with
    | there v1 =>
      cases v1 with
      | here =>
        rw [resolveVar_trip_idx, evalOperandN, pullM_getW]
        show ((cmpB0 sa).setReg (loopIdx 4) (0#64)).reg.getW (cmpTau (argName 3)) 64 = _
        rw [cmpTau_a3, LstateM.reg_setReg, LstateN.getW_setReg_same]
        rfl
      | there u =>
        cases u with
        | there u1 => cases u1 with
          | there u2 => cases u2 with
            | here =>
              show ((cmpB0 sa).setReg (loopIdx 4) (0#64)).reg.getW (cmpTau (argName 0)) 64 = _
              rw [cmpTau_arg (by decide), LstateM.reg_setReg,
                LstateN.getW_setReg_other _ _ _ _ _ (loopIdx_ne_argName 4 0).symm,
                show argName 0 = "a0" from rfl, ← hc]
              exact (entryM_getW (v := sa.regs "%rcx")
              (by simp (config := { decide := true }) [List.lookup])).trans rfl
            | there u3 => cases u3
  · cases v with
    | here =>
      rw [resolveVar_trip_acc]
      simp only [operandName, pullM_getArr]
      show ((cmpB0 sa).setReg (loopIdx 4) (0#64)).getArr (cmpTau (argName 4)) 64 1 = _
      rw [cmpTau_a4, getArr_setReg]
      exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
    | there v1 =>
      cases v1 with
      | there u =>
        cases u with
        | here =>
          show ((cmpB0 sa).setReg (loopIdx 4) (0#64)).getArr (cmpTau (argName 2)) 64 8 = _
          rw [cmpTau_arg (by decide), getArr_setReg, show argName 2 = "a2" from rfl]
          exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
        | there u1 =>
          cases u1 with
          | here =>
            show ((cmpB0 sa).setReg (loopIdx 4) (0#64)).getArr (cmpTau (argName 1)) 64 8 = _
            rw [cmpTau_arg (by decide), getArr_setReg, show argName 1 = "a1" from rfl]
            exact entryM_getArr (by simp (config := { decide := true }) [List.lookup])
          | there u2 =>
            cases u2 with
            | there u3 => cases u3

/-- **`mpn_cmp_ct` from the machine entry.** The program and its decoded function bytes as
    in `mpn_cmp_ct_bytes_correct`; from every machine state with `rp`, `ap`, `bp` and the
    count `0 < m ≤ 8` in `%rdi`, `%rsi`, `%rdx`, `%rcx` and the entry word at `rp` zero (the
    seed of the model), under the separation hypotheses, the machine halts with the sign
    of the comparison of the `m`-word numbers at `ap` and `bp` at `rp`. -/
theorem mpn_cmp_ct_entry_correct :
    ∃ f : Lfundef,
      (MpnCmpFrontEmit.cmpRtLprogOpt "mpn_cmp_ct").map (·.lp_funcs) = some [("mpn_cmp_ct", f)]
      ∧ ∃ prog, decodeLprog (encodeLfundefBytes f.lfd_body) = some prog
      ∧ ∀ (rp app bpp rsp : BitVec 64) (m : Nat), 0 < m → m ≤ 8 →
        (cmpLay rp app bpp).Sep (cmpFrame rsp) → cmpDis rp app bpp →
        cmpStackSep rp app bpp rsp →
        ∀ sa : AState, cmpEntry rp app bpp rsp m sa → wd sa rp 0 = 0 →
        ∃ sa', Halts aMachine prog 0 sa sa'
          ∧ read64 sa'.mem rp
              = cmpSign (bignumVal ((List.range m).map (wd sa app)))
                  (bignumVal ((List.range m).map (wd sa bpp))) := by
  obtain ⟨f, hf, prog, hdec, H⟩ := mpn_cmp_ct_bytes_correct
  refine ⟨f, hf, prog, hdec, fun rp app bpp rsp m hm0 hm hsep hdis hstk sa hE h0 => ?_⟩
  have hw0 : memGetDyn (wordsAt sa (sa.regs "%rdi") 1) 0 = 0 := by
    rw [memGetDyn_wordsAt (by decide), hE.2.1]; exact h0
  obtain ⟨sa', hh, hw⟩ := H rp app bpp rsp m hm0 hm hsep hdis hstk sa (cmpB0 sa) false
    entryM_lpc (cmpB0_corr rp app bpp rsp m sa hE false) hE _ _ _ hw0
    (cmpB0_seed sa m hE.2.2.2.2)
  refine ⟨sa', hh, ?_⟩
  rw [segCells_wordsAt (show m ≤ 8 from hm), segCells_wordsAt (show m ≤ 8 from hm),
    hE.2.2.1, hE.2.2.2.1] at hw
  exact hw

end Cmp

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnChainEntry
