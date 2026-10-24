/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSubP

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the whole 4-limb Montgomery multiply

`Curve4MontMulProvenEmit.montMulProvenBlock limbImms nprime` is
`loadInputs ++ loadConsts ++ clearAccs ++ emitProductBlock4 ++ emitMontRedc4Block
++ emitCondSubP ++ storeOutputs`. The three arithmetic cores each carry a proven
block agreement (`emitProductBlock4_lsem_agree`, `emitMontRedc4Block_lsem_agree`,
`emitCondSubP_lsem_agree`). This module bridges the scaffolding stages
(`loadInputs`/`loadConsts`/`clearAccs`/`storeOutputs`) and threads all seven
stages into one whole-block agreement between the total `runBlock` fold and its
lsem lowering.

## The scaffolding stages

`loadInputs` and `storeOutputs` are compile-time-offset word memory ops
(`.loadMem` / `.storeMem` with a non-negative displacement), lowered to the
`.loadC` / `.storeC` `MOVQ` twins and bridged by the memory-agreement axis.
`loadConsts` is a list of immediate `MOV`s. Each of these ops writes a data
register or a memory cell and leaves the designated width-1 `CF` slot untouched,
so they preserve `JLstateCorrCF` at the entry slot (`loadMem_caseCF`,
`movImm_caseCF`, `storeMem_caseCF`, lifted over a list by `cfList_agree`).

`clearAccs` is a list of self-`xor`s (`t0..t7`, then `rtop`), whose final
`xor rtop, rtop` resets `CF = OF = 0`. Its lowering appends the width-1
zero-slot production (`MOV z, 0`; two `ADCXHI zc ← z, z, cfN` writing
`carryOutBit 0 0 _ = 0`) mirroring the reset pair, so the stage moves from
`JLstateCorrCF` at the entry slot to `JLstateCorrF` at the freshly-zeroed pair —
the flag-reset entry the product core requires.

## The entry correspondence

The first zero-slot production reads a junk carry-in from an incoming width-1
slot, which the register-and-memory-only `JLstateCorr` cannot supply. The
whole-block agreement therefore enters at `JLstateCorrCF s ls flg cfIn` (the
prologue's zeroed flag slot).

## Main results

* `movImm_caseCF` / `loadMem_caseCF` / `storeMem_caseCF`: per-opcode `CF`-track
  agreement for the immediate `MOV`, the compile-time load, and the compile-time
  store, each preserving the designated slot.
* `cfList_agree`: the list lift of a slot-preserving per-opcode agreement.
* `loadInputs_lsem_agree` / `loadConsts_lsem_agree` / `storeOutputs_lsem_agree`:
  the scaffolding list stages, preserving the entry slot.
* `selfXorList_raw` / `clearPair_case` / `clearAccs_lsem_agree`: the self-`xor`
  clear with the zero-pair production, moving `JLstateCorrCF` to `JLstateCorrF`.
* `montMulProvenBlock_lsem_agree`: the whole-block agreement.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontMulBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSub
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeColumnReset
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontRedc
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeCondSubP
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Per-opcode `CF`-track agreement for the scaffolding opcodes -/

/-- **Per-opcode agreement for `.mov dst (.imm n)` under `JLstateCorrCF`.** The
    immediate `MOV` writes one data register and touches no flag, so the
    designated slot `cfN` carries over. -/
theorem movImm_caseCF (flg : String → Prop) (cfN dst : String) (n : Nat)
    (hDst : ¬ flg dst) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem [jToRM (.mov dst (.imm n))] ls = some ls' ∧
        JLstateCorrCF (runBlock s [.mov dst (.imm n)]) ls' flg cfN := by
  intro s ls hcorr
  refine ⟨_, ?_, JLstateCorrCF_setReg s _ ls flg cfN hcorr dst (BitVec.ofNat 64 n) hDst ?_ ?_ ?_⟩
  · show lsemStraightMem
      [(.Lopn [.reg dst] (withWidthTag 64 "MOV") [.imm n], MemTag.reg none)] ls = _
    rw [lsemStraightMem_single]
    exact lsemStepMem_movImm dst n ls
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.setReg]
  · intro base off
    simp only [runBlock_cons, runBlock_nil, evalInstr, JState.setReg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg]

/-- **Per-opcode agreement for `.loadMem dst base off` under `JLstateCorrCF`.**
    For a non-negative displacement, the `.loadC`-tagged `MOVQ` twin loads
    `s.mem base off` (memory-agreement half) into the data register `dst` and
    leaves the designated slot `cfN` untouched. -/
theorem loadMem_caseCF (flg : String → Prop) (cfN dst base : String) (off : Int)
    (hoff : 0 ≤ off) (hDst : ¬ flg dst) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem [jToRM (.loadMem dst base off)] ls = some ls' ∧
        JLstateCorrCF (runBlock s [.loadMem dst base off]) ls' flg cfN := by
  intro s ls hcorr
  have hio : (Int.ofNat off.toNat) = off := Int.toNat_of_nonneg hoff
  have hV : ls.lmem base (Int.ofNat off.toNat) = s.mem base off := by
    rw [hio]; exact hcorr.memAgree base off
  refine ⟨(ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc, ?_, ?_⟩
  · show lsemStraightMem [(.Lopn [.reg dst] "MOVQ" [.arr base off.toNat], .loadC)] ls = _
    rw [lsemStraightMem_single, lsemStepMem_loadC]
  · refine ⟨?_, ?_, ?_, hcorr.cfFlg⟩
    · intro r hr
      show ((ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc).reg.getW r 64
        = some ((runBlock s [.loadMem dst base off]).regs r)
      rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
      have hrhs : (runBlock s [.loadMem dst base off]).regs r
          = if r = dst then s.mem base off else s.regs r := by
        simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.load]
      rw [hrhs]
      by_cases hrd : r = dst
      · subst hrd; rw [LstateN.getW_setReg_same, hV, ite_eq_left rfl]
      · rw [LstateN.getW_setReg_other _ _ _ _ _ hrd, hcorr.regAgree r hr, ite_eq_right hrd]
    · intro base' off'
      show ((ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc).lmem base' off'
        = (runBlock s [.loadMem dst base off]).mem base' off'
      rw [LstateM.lmem_nextPc, LstateM.lmem_setReg]
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.load]
      exact hcorr.memAgree base' off'
    · show ((ls.setReg dst (ls.lmem base (Int.ofNat off.toNat))).nextPc).reg.getW cfN 1
        = some (flagBit ((runBlock s [.loadMem dst base off]).flagB (·.cf)))
      rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
      have hcf : (runBlock s [.loadMem dst base off]).flagB (·.cf) = s.flagB (·.cf) := by
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, x86_MOV, JState.setReg,
          JState.load]
      have hdcf : dst ≠ cfN := fun h => hDst (h ▸ hcorr.cfFlg)
      rw [hcf, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdcf)]
      exact hcorr.cfAgree

/-- **Per-opcode agreement for `.storeMem base off (.reg src)` under
    `JLstateCorrCF`.** For a non-negative displacement the `.storeC`-tagged `MOVQ`
    twin writes `s.regs src` into memory cell `[base + off]` and leaves every
    register (the designated slot `cfN` included) untouched. -/
theorem storeMem_caseCF (flg : String → Prop) (cfN base : String) (off : Int) (src : String)
    (hoff : 0 ≤ off) (hSrc : ¬ flg src) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem [jToRM (.storeMem base off (.reg src))] ls = some ls' ∧
        JLstateCorrCF (runBlock s [.storeMem base off (.reg src)]) ls' flg cfN := by
  intro s ls hcorr
  have hio : (Int.ofNat off.toNat) = off := Int.toNat_of_nonneg hoff
  refine ⟨(ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc, ?_, ?_⟩
  · show lsemStraightMem [(.Lopn [.arr base off.toNat] "MOVQ" [.reg src], .storeC)] ls = _
    rw [lsemStraightMem_single,
      lsemStepMem_storeC base off.toNat src ls (s.regs src) (hcorr.regAgree src hSrc)]
  · refine ⟨?_, ?_, ?_, hcorr.cfFlg⟩
    · intro r hr
      show ((ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc).reg.getW r 64
        = some ((runBlock s [.storeMem base off (.reg src)]).regs r)
      rw [LstateM.reg_nextPc, LstateM.reg_storeMemC, LstateN.getW_nextPc, hcorr.regAgree r hr]
      simp only [runBlock_cons, runBlock_nil, evalInstr, JState.regs_store]
    · intro base' off'
      show ((ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc).lmem base' off'
        = (runBlock s [.storeMem base off (.reg src)]).mem base' off'
      rw [LstateM.lmem_nextPc, hio]
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval, JState.get,
        JState.store, LstateM.storeMemC]
      split_ifs with h
      · rfl
      · exact hcorr.memAgree base' off'
    · show ((ls.storeMemC base (Int.ofNat off.toNat) (s.regs src)).nextPc).reg.getW cfN 1
        = some (flagBit ((runBlock s [.storeMem base off (.reg src)]).flagB (·.cf)))
      rw [LstateM.reg_nextPc, LstateM.reg_storeMemC, LstateN.getW_nextPc]
      have hcf : (runBlock s [.storeMem base off (.reg src)]).flagB (·.cf) = s.flagB (·.cf) := by
        simp only [runBlock_cons, runBlock_nil, evalInstr, JState.flagB, JState.store]
      rw [hcf]; exact hcorr.cfAgree

/-! ## 2. The slot-preserving list lift -/

/-- **List lift of a slot-preserving per-opcode agreement.** Every opcode of `js`
    lowers one-to-one under `f` and preserves `JLstateCorrCF` at the fixed slot
    `cfN`; the whole list then runs to completion and preserves it. Straight-line
    induction, each element composed with `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem cfList_agree (flg : String → Prop) (cfN : String) (f : JInstr 64 → LinstrRM)
    (js : List (JInstr 64))
    (hper : ∀ i ∈ js, ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
       ∃ ls', lsemStraightMem [f i] ls = some ls' ∧ JLstateCorrCF (runBlock s [i]) ls' flg cfN) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (js.map f) ls = some ls' ∧
        JLstateCorrCF (runBlock s js) ls' flg cfN := by
  induction js with
  | nil => intro s ls h; exact ⟨ls, rfl, h⟩
  | cons i is ih =>
    have hi := hper i (List.mem_cons_self ..)
    have htail := ih (fun j hj => hper j (List.mem_cons_of_mem i hj))
    have hcomp := runBlock_lsem_agreeCF_seq_migrate [i] is [f i] (is.map f) flg cfN cfN cfN hi htail
    intro s ls h
    simpa only [List.map_cons, List.singleton_append] using hcomp s ls h

/-! ## 3. The `loadInputs` / `loadConsts` / `storeOutputs` stages -/

/-- **Block agreement for `loadInputs`.** The eight compile-time-offset word
    loads preserve `JLstateCorrCF` at the entry slot `cfN`. -/
theorem loadInputs_lsem_agree (flg : String → Prop) (cfN : String)
    (hx0 : ¬ flg "x0") (hx1 : ¬ flg "x1") (hx2 : ¬ flg "x2") (hx3 : ¬ flg "x3")
    (hy0 : ¬ flg "y0") (hy1 : ¬ flg "y1") (hy2 : ¬ flg "y2") (hy3 : ¬ flg "y3") :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (loadInputs.map jToRM) ls = some ls' ∧
        JLstateCorrCF (runBlock s loadInputs) ls' flg cfN := by
  apply cfList_agree flg cfN jToRM loadInputs
  intro i hi
  rw [loadInputs, List.mem_append] at hi
  have hoffj : ∀ j : Nat, (0:Int) ≤ 8 * (j:Int) := fun j => by positivity
  rcases hi with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    have hj4 : j < 4 := List.mem_range.1 hj
    refine loadMem_caseCF flg cfN _ "x" _ (hoffj j) ?_
    interval_cases j
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    have hj4 : j < 4 := List.mem_range.1 hj
    refine loadMem_caseCF flg cfN _ "y" _ (hoffj j) ?_
    interval_cases j
    · exact hy0
    · exact hy1
    · exact hy2
    · exact hy3

/-- **Block agreement for `loadConsts`.** The four modulus-limb immediate `MOV`s
    and the `n'` immediate `MOV` preserve `JLstateCorrCF` at the entry slot
    `cfN`. -/
theorem loadConsts_lsem_agree (flg : String → Prop) (cfN : String)
    (limbImms : List Nat) (nprime : Nat)
    (hp0 : ¬ flg "p0") (hp1 : ¬ flg "p1") (hp2 : ¬ flg "p2") (hp3 : ¬ flg "p3")
    (hnp : ¬ flg npName) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem ((loadConsts limbImms nprime).map jToRM) ls = some ls' ∧
        JLstateCorrCF (runBlock s (loadConsts limbImms nprime)) ls' flg cfN := by
  apply cfList_agree flg cfN jToRM (loadConsts limbImms nprime)
  intro i hi
  rw [loadConsts, List.mem_append] at hi
  rcases hi with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    have hj4 : j < 4 := List.mem_range.1 hj
    refine movImm_caseCF flg cfN _ _ ?_
    interval_cases j
    · exact hp0
    · exact hp1
    · exact hp2
    · exact hp3
  · rw [List.mem_singleton] at h
    subst h
    exact movImm_caseCF flg cfN npName nprime hnp

/-- **Block agreement for `storeOutputs`.** The four compile-time-offset word
    stores of the canonical result limbs preserve `JLstateCorrCF` at the entry
    slot `cfN`. -/
theorem storeOutputs_lsem_agree (flg : String → Prop) (cfN : String)
    (hr0 : ¬ flg "r0") (hr1 : ¬ flg "r1") (hr2 : ¬ flg "r2") (hr3 : ¬ flg "r3") :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (storeOutputs.map jToRM) ls = some ls' ∧
        JLstateCorrCF (runBlock s storeOutputs) ls' flg cfN := by
  apply cfList_agree flg cfN jToRM storeOutputs
  intro i hi
  rw [storeOutputs] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  have hj4 : j < 4 := List.mem_range.1 hj
  have hoffj : (0:Int) ≤ 8 * (j:Int) := by positivity
  refine storeMem_caseCF flg cfN "z" _ _ hoffj ?_
  interval_cases j
  · exact hr0
  · exact hr1
  · exact hr2
  · exact hr3

/-! ## 4. The self-`xor` clear with the zero-pair production -/

/-- The lsem wire of a self-`xor`: the two-address `XOR` data wire on one
    register. -/
def selfXorWire (r : String) : LinstrRM :=
  (.Lopn [.reg r] (withWidthTag 64 "XOR") [.reg r, .reg r], MemTag.reg none)

/-- The source of a self-`xor` list: one `xor r, r` per register. -/
def selfXorListJ (rs : List String) : List (JInstr 64) :=
  rs.map (fun r => JInstr.xor_ r (.reg r))

/-- The width-1 zero-slot production appended after a self-`xor` clear: `MOV z, 0`
    and two `ADCXHI zc ← z, z, cfN` writing `carryOutBit 0 0 _ = 0` to the fresh
    slots `zc1` / `zc2`, mirroring the reset `CF` / `OF`. -/
def clearPairTailL (z cfN zc1 zc2 : String) : List LinstrRM :=
  [ (movImmLinstr 64 z 0, MemTag.reg none),
    (.Lopn [.reg zc1] (withWidthTag 64 "ADCXHI") [.reg z, .reg z, .reg cfN], MemTag.reg none),
    (.Lopn [.reg zc2] (withWidthTag 64 "ADCXHI") [.reg z, .reg z, .reg cfN], MemTag.reg none) ]

/-- The self-`xor` list preserves register agreement off the flag namespace,
    memory agreement, and the width-1 read of the flag-name slot `cfN` (whose
    value is untouched). Straight-line induction, each self-`xor` via
    `xorSelf_case` and `regAgree_setReg_matched`. -/
theorem selfXorList_raw (flg : String → Prop) (cfN : String) (hcfN : flg cfN) (vc : BitVec 1) :
    ∀ (rs : List String), (∀ r ∈ rs, ¬ flg r) →
      ∀ (s : JState 64) (ls : LstateM),
        (∀ r, ¬ flg r → ls.reg.getW r 64 = some (s.regs r)) →
        (∀ (base : String) (off : Int), ls.lmem base off = s.mem base off) →
        ls.reg.getW cfN 1 = some vc →
        ∃ ls', lsemStraightMem (rs.map selfXorWire) ls = some ls' ∧
          (∀ r, ¬ flg r → ls'.reg.getW r 64 = some ((runBlock s (selfXorListJ rs)).regs r)) ∧
          (∀ (base : String) (off : Int),
            ls'.lmem base off = (runBlock s (selfXorListJ rs)).mem base off) ∧
          ls'.reg.getW cfN 1 = some vc := by
  intro rs
  induction rs with
  | nil =>
    intro _ s ls hreg hmem hcf
    refine ⟨ls, rfl, ?_, ?_, hcf⟩
    · simpa only [selfXorListJ, List.map_nil, runBlock_nil] using hreg
    · simpa only [selfXorListJ, List.map_nil, runBlock_nil] using hmem
  | cons r rs ih =>
    intro hrs s ls hreg hmem hcf
    have hr : ¬ flg r := hrs r (List.mem_cons_self ..)
    have hrcf : r ≠ cfN := fun h => hr (h ▸ hcfN)
    have e := xorSelf_case s ls flg hreg r hr
    set s1 : JState 64 := evalInstr s (JInstr.xor_ r (.reg r)) with hs1
    set ls1 : LstateM :=
      { ls with reg := (ls.reg.setReg r ((x86_XOR (s.regs r) (s.regs r)).word)).nextPc } with hls1
    have hs1r : ∀ q, s1.regs q =
        if q = r then (x86_XOR (s.regs r) (s.regs r)).word else s.regs q := by
      intro q; rw [hs1]; simp only [evalInstr, JState.writeB5W, JOperand.eval, JState.get]
    have hreg1 : ∀ q, ¬ flg q → ls1.reg.getW q 64 = some (s1.regs q) :=
      regAgree_setReg_matched s ls flg hreg s1 r _ hs1r
    have hmem1 : ∀ (base : String) (off : Int), ls1.lmem base off = s1.mem base off := by
      intro base off
      show ls.lmem base off = s1.mem base off
      rw [hs1]; simp only [evalInstr, JState.writeB5W]; exact hmem base off
    have hcf1 : ls1.reg.getW cfN 1 = some vc := by
      show ((ls.reg.setReg r _).nextPc).getW cfN 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hrcf)]; exact hcf
    obtain ⟨ls', etail, hrf, hmf, hcff⟩ :=
      ih (fun q hq => hrs q (List.mem_cons_of_mem r hq)) s1 ls1 hreg1 hmem1 hcf1
    have hrun : runBlock s (selfXorListJ (r :: rs)) = runBlock s1 (selfXorListJ rs) := by
      rw [hs1]; simp only [selfXorListJ, List.map_cons, runBlock_cons]
    refine ⟨ls', ?_, ?_, ?_, hcff⟩
    · simp only [List.map_cons, lsemStraightMem_cons, selfXorWire, e]
      exact etail
    · intro q hq; rw [hrun]; exact hrf q hq
    · intro base off; rw [hrun]; exact hmf base off

/-- The final `CF` flag after a self-`xor` list ending in `last` is `0`: the last
    `xor last, last` routes through `x86_XOR`, which resets `CF`. -/
theorem selfXorAppendLast_cf_false (s : JState 64) (rs : List String) (last : String) :
    (runBlock s (selfXorListJ (rs ++ [last]))).flagB (·.cf) = false := by
  have hsplit : selfXorListJ (rs ++ [last])
      = selfXorListJ rs ++ [JInstr.xor_ last (.reg last)] := by
    simp only [selfXorListJ, List.map_append, List.map_cons, List.map_nil]
  rw [hsplit, Jasmin.runBlock_append, Jasmin.runBlock_cons, Jasmin.runBlock_nil]
  exact flagB_cf_xorSelf (runBlock s (selfXorListJ rs)) last

/-- The final `OF` flag after a self-`xor` list ending in `last` is `0`: the last
    `xor last, last` routes through `x86_XOR`, which resets `OF`. -/
theorem selfXorAppendLast_of_false (s : JState 64) (rs : List String) (last : String) :
    (runBlock s (selfXorListJ (rs ++ [last]))).flagB (·.of) = false := by
  have hsplit : selfXorListJ (rs ++ [last])
      = selfXorListJ rs ++ [JInstr.xor_ last (.reg last)] := by
    simp only [selfXorListJ, List.map_append, List.map_cons, List.map_nil]
  rw [hsplit, Jasmin.runBlock_append, Jasmin.runBlock_cons, Jasmin.runBlock_nil]
  exact flagB_of_xorSelf (runBlock s (selfXorListJ rs)) last

/-- **Block agreement for a self-`xor` clear with the zero-pair production.** From
    a `JLstateCorrCF` entry at `cfN`, the self-`xor` list `rs ++ [last]` followed
    by the zero-pair tail moves to `JLstateCorrF` at the freshly-zeroed pair
    `(zc1, zc2)`, which mirrors the `CF = OF = 0` the final `xor last, last`
    establishes. -/
theorem clearPair_case (flg : String → Prop) (cfN z zc1 zc2 : String)
    (rs : List String) (last : String)
    (hrs : ∀ r ∈ rs, ¬ flg r) (hlast : ¬ flg last)
    (hz : flg z) (hzc1 : flg zc1) (hzc2 : flg zc2) (hcfN : flg cfN)
    (hzcf : z ≠ cfN) (h1z : zc1 ≠ z) (h1cf : zc1 ≠ cfN) (h21 : zc2 ≠ zc1) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem
          ((rs ++ [last]).map selfXorWire ++ clearPairTailL z cfN zc1 zc2) ls = some ls' ∧
        JLstateCorrF (runBlock s (selfXorListJ (rs ++ [last]))) ls' flg zc1 zc2 := by
  intro s ls hcorr
  have hmem_rl : ∀ r ∈ rs ++ [last], ¬ flg r := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hrs r h
    · rcases List.mem_singleton.1 h with rfl; exact hlast
  obtain ⟨ls1, eraw, hrf, hmf, hcff⟩ :=
    selfXorList_raw flg cfN hcfN (flagBit (s.flagB (·.cf))) (rs ++ [last]) hmem_rl s ls
      hcorr.regAgree hcorr.memAgree hcorr.cfAgree
  set s' : JState 64 := runBlock s (selfXorListJ (rs ++ [last])) with hs'
  have hcfv : s'.flagB (·.cf) = false := selfXorAppendLast_cf_false s rs last
  have hofv : s'.flagB (·.of) = false := selfXorAppendLast_of_false s rs last
  -- Step: `MOV z, 0`.
  have e4 : lsemStepMem (movImmLinstr 64 z 0, MemTag.reg none) ls1
      = some { ls1 with reg := (ls1.reg.setReg z (BitVec.ofNat 64 0)).nextPc } :=
    lsemStepMem_movImm z 0 ls1
  set ls4 : LstateM := { ls1 with reg := (ls1.reg.setReg z (BitVec.ofNat 64 0)).nextPc } with hls4
  have hz4 : ls4.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls1.reg.setReg z _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hcf4 : ls4.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls1.reg.setReg z _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]
    exact hcff
  -- Step: `ADCXHI zc1 ← z, z, cfN` — the `CF` zero slot.
  have e5 := lsemStepMem_adcxhi3 zc1 z z cfN ls4 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz4 hz4 hcf4
  set ls5 : LstateM :=
    { ls4 with reg := (ls4.reg.setReg zc1
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls5
  have hz5 : ls5.reg.getW z 64 = some (BitVec.ofNat 64 0) := by
    show ((ls4.reg.setReg zc1 _).nextPc).getW z 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h1z)]
    exact hz4
  have hcf5 : ls5.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    show ((ls4.reg.setReg zc1 _).nextPc).getW cfN 1 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h1cf)]
    exact hcf4
  -- Step: `ADCXHI zc2 ← z, z, cfN` — the `OF` zero slot.
  have e6 := lsemStepMem_adcxhi3 zc2 z z cfN ls5 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (flagBit (s.flagB (·.cf))) hz5 hz5 hcf5
  set ls6 : LstateM :=
    { ls5 with reg := (ls5.reg.setReg zc2
        (carryOutBit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls6
  refine ⟨ls6, ?_, ?_⟩
  · rw [lsemStraightMem_append, eraw, Option.bind]
    simp only [clearPairTailL, lsemStraightMem_cons, e4, e5, e6, lsemStraightMem_nil]
  · refine ⟨?_, ?_, ?_, ?_, hzc1, hzc2, Ne.symm h21⟩
    · intro r hr
      have hr1 : r ≠ zc1 := fun h => hr (h ▸ hzc1)
      have hr2 : r ≠ zc2 := fun h => hr (h ▸ hzc2)
      have hrz : r ≠ z := fun h => hr (h ▸ hz)
      show ((ls5.reg.setReg zc2 _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hr2]
      show ((ls4.reg.setReg zc1 _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hr1]
      show ((ls1.reg.setReg z _).nextPc).getW r 64 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hrz]
      exact hrf r hr
    · intro base off
      exact hmf base off
    · show ((ls5.reg.setReg zc2 _).nextPc).getW zc1 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm h21)]
      show ((ls4.reg.setReg zc1 _).nextPc).getW zc1 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero, hcfv]
    · show ((ls5.reg.setReg zc2 _).nextPc).getW zc2 1 = _
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_same, carryOutBit_zero_zero, hofv]

/-- `clearAccs` is the self-`xor` list over the accumulator names followed by the
    top-word `rtop`. -/
theorem clearAccs_eq : clearAccs = selfXorListJ (accNames ++ [rtopName]) := by
  simp only [clearAccs, selfXorListJ, List.map_append, List.map_cons, List.map_nil]

/-- The lsem lowering of `clearAccs`: the nine self-`XOR` wires and the zero-pair
    production reseeding the `CF` / `OF` slots `zc1` / `zc2`. -/
def clearAccsL (z cfN zc1 zc2 : String) : List LinstrRM :=
  (accNames ++ [rtopName]).map selfXorWire ++ clearPairTailL z cfN zc1 zc2

/-- **Block agreement for `clearAccs`.** From a `JLstateCorrCF` entry at `cfN`, the
    accumulator clear moves to `JLstateCorrF` at the freshly-zeroed pair
    `(zc1, zc2)`. -/
theorem clearAccs_lsem_agree (flg : String → Prop) (cfN z zc1 zc2 : String)
    (ht0 : ¬ flg "t0") (ht1 : ¬ flg "t1") (ht2 : ¬ flg "t2") (ht3 : ¬ flg "t3")
    (ht4 : ¬ flg "t4") (ht5 : ¬ flg "t5") (ht6 : ¬ flg "t6") (ht7 : ¬ flg "t7")
    (hrtop : ¬ flg rtopName)
    (hz : flg z) (hzc1 : flg zc1) (hzc2 : flg zc2) (hcfN : flg cfN)
    (hzcf : z ≠ cfN) (h1z : zc1 ≠ z) (h1cf : zc1 ≠ cfN) (h21 : zc2 ≠ zc1) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (clearAccsL z cfN zc1 zc2) ls = some ls' ∧
        JLstateCorrF (runBlock s clearAccs) ls' flg zc1 zc2 := by
  have hrs : ∀ r ∈ accNames, ¬ flg r := by
    intro r hr
    have hacc : accNames = ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7"] := rfl
    rw [hacc] at hr
    fin_cases hr <;>
      first | exact ht0 | exact ht1 | exact ht2 | exact ht3
            | exact ht4 | exact ht5 | exact ht6 | exact ht7
  intro s ls hcorr
  rw [clearAccs_eq]
  exact clearPair_case flg cfN z zc1 zc2 accNames rtopName hrs hrtop hz hzc1 hzc2 hcfN
    hzcf h1z h1cf h21 s ls hcorr

/-! ## 5. The whole-block agreement -/

/-- The lsem lowering of the whole 4-limb Montgomery multiply block, threading the
    seven stages through the scaffolding slots and the three arithmetic cores'
    slot data. -/
def montMulProvenBlockL (limbImms : List Nat) (nprime : Nat)
    (z cfIn zc1 zc2 : String)
    (slotss : List (List ((String × String) × (String × String))))
    (sl0 sl1 sl2 sl3 : StepSlots)
    (zc fr0 fr1 fr2 fr3 fr4 : String) : List LinstrRM :=
  loadInputs.map jToRM
    ++ (loadConsts limbImms nprime).map jToRM
    ++ clearAccsL z cfIn zc1 zc2
    ++ prodResetL z hiName loName zc1 zc2 accNames xNames yNames slotss
    ++ montRedc4L z (prodFinal (zc1, zc2) slotss).1 sl0 sl1 sl2 sl3
    ++ emitCondSubPL z zc (stepFinal sl3) fr0 fr1 fr2 fr3 fr4
    ++ storeOutputs.map jToRM

/-- **Block agreement for the whole 4-limb Montgomery multiply.** From a
    `JLstateCorrCF` entry at the prologue slot `cfIn`, `montMulProvenBlock` over
    `runBlock` corresponds to `montMulProvenBlockL` run to completion (TOTALITY),
    landing in `JLstateCorrCF` at the canonicalisation's fixed slot
    `stepFinal sl3`. The four scaffolding stages preserve or establish the slot
    correspondence; the three arithmetic cores are the proven
    `emitProductBlock4_lsem_agree`, `emitMontRedc4Block_lsem_agree`, and
    `emitCondSubP_lsem_agree`; the stages are composed with `agree_seq_corr`. -/
theorem montMulProvenBlock_lsem_agree (flg : String → Prop)
    (limbImms : List Nat) (nprime : Nat)
    (z cfIn zc1 zc2 : String)
    (slotss : List (List ((String × String) × (String × String))))
    (sl0 sl1 sl2 sl3 : StepSlots)
    (zc fr0 fr1 fr2 fr3 fr4 : String)
    -- scaffolding data registers off the flag namespace
    (hx0 : ¬ flg "x0") (hx1 : ¬ flg "x1") (hx2 : ¬ flg "x2") (hx3 : ¬ flg "x3")
    (hy0 : ¬ flg "y0") (hy1 : ¬ flg "y1") (hy2 : ¬ flg "y2") (hy3 : ¬ flg "y3")
    (hp0 : ¬ flg "p0") (hp1 : ¬ flg "p1") (hp2 : ¬ flg "p2") (hp3 : ¬ flg "p3")
    (hnp : ¬ flg npName)
    (ht0 : ¬ flg "t0") (ht1 : ¬ flg "t1") (ht2 : ¬ flg "t2") (ht3 : ¬ flg "t3")
    (ht4 : ¬ flg "t4") (ht5 : ¬ flg "t5") (ht6 : ¬ flg "t6") (ht7 : ¬ flg "t7")
    (hrtop : ¬ flg rtopName)
    (hr0 : ¬ flg "r0") (hr1 : ¬ flg "r1") (hr2 : ¬ flg "r2") (hr3 : ¬ flg "r3")
    -- clear-pair slot freshness
    (hz : flg z) (hzc1 : flg zc1) (hzc2 : flg zc2) (hcfIn : flg cfIn)
    (hzcf : z ≠ cfIn) (h1z : zc1 ≠ z) (h1cf : zc1 ≠ cfIn) (h21 : zc2 ≠ zc1)
    -- the product / reduce / canonicalisation core freshness
    (hprod : ProdResetFresh flg z hiName loName zc1 zc2 accNames xNames yNames slotss)
    (hf0 : StepFreshAt flg z 0 (prodFinal (zc1, zc2) slotss).1 sl0)
    (hf1 : StepFreshAt flg z 1 (stepFinal sl0) sl1)
    (hf2 : StepFreshAt flg z 2 (stepFinal sl1) sl2)
    (hf3 : StepFreshAt flg z 3 (stepFinal sl2) sl3)
    (hcsub : CondSubPFresh flg z zc (stepFinal sl3) fr0 fr1 fr2 fr3 fr4) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfIn →
      ∃ ls', lsemStraightMem
          (montMulProvenBlockL limbImms nprime z cfIn zc1 zc2 slotss sl0 sl1 sl2 sl3
            zc fr0 fr1 fr2 fr3 fr4) ls = some ls' ∧
        JLstateCorrCF (runBlock s (montMulProvenBlock limbImms nprime)) ls' flg (stepFinal sl3) := by
  -- Stage lemmas, each in the `∀ s ls, Rel → …` shape.
  have hLoad := loadInputs_lsem_agree flg cfIn hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3
  have hConsts := loadConsts_lsem_agree flg cfIn limbImms nprime hp0 hp1 hp2 hp3 hnp
  have hClear := clearAccs_lsem_agree flg cfIn z zc1 zc2 ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 hrtop
    hz hzc1 hzc2 hcfIn hzcf h1z h1cf h21
  have hProd : ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg zc1 zc2 →
      ∃ ls', lsemStraightMem
          (prodResetL z hiName loName zc1 zc2 accNames xNames yNames slotss) ls = some ls' ∧
        JLstateCorrCF (runBlock s (emitProductBlock4 accNames xNames yNames hiName loName)) ls'
          flg (prodFinal (zc1, zc2) slotss).1 := by
    intro s ls h
    obtain ⟨ls', e', c'⟩ :=
      emitProductBlock4_lsem_agree flg z hiName loName yNames slotss accNames xNames zc1 zc2
        hprod s ls h
    exact ⟨ls', e', JLstateCorrCF_of_F _ _ flg _ _ c'⟩
  have hReduce := fun (s : JState 64) (ls : LstateM)
      (h : JLstateCorrCF s ls flg (prodFinal (zc1, zc2) slotss).1) =>
    emitMontRedc4Block_lsem_agree flg z (prodFinal (zc1, zc2) slotss).1 sl0 sl1 sl2 sl3
      hf0 hf1 hf2 hf3 s ls h
  have hCond := emitCondSubP_lsem_agree flg z zc (stepFinal sl3) fr0 fr1 fr2 fr3 fr4 hcsub
  have hStore := storeOutputs_lsem_agree flg (stepFinal sl3) hr0 hr1 hr2 hr3
  -- Compose the seven stages.
  have c01 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg cfIn)
    (R := fun s ls => JLstateCorrCF s ls flg cfIn)
    _ _ _ _ hLoad hConsts
  have c012 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg cfIn)
    (R := fun s ls => JLstateCorrF s ls flg zc1 zc2)
    _ _ _ _ c01 hClear
  have c0123 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrF s ls flg zc1 zc2)
    (R := fun s ls => JLstateCorrCF s ls flg (prodFinal (zc1, zc2) slotss).1)
    _ _ _ _ c012 hProd
  have c01234 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg (prodFinal (zc1, zc2) slotss).1)
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    _ _ _ _ c0123 hReduce
  have c012345 := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    _ _ _ _ c01234 hCond
  have call := agree_seq_corr
    (P := fun s ls => JLstateCorrCF s ls flg cfIn)
    (Q := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    (R := fun s ls => JLstateCorrCF s ls flg (stepFinal sl3))
    _ _ _ _ c012345 hStore
  intro s ls h
  simpa only [montMulProvenBlock, montMulProvenBlockL] using call s ls h

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMontMulBlock
