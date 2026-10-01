/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV
public import Std.Data.String.ToInt

@[expose] public section

set_option autoImplicit false

/-!
# The soundness of the read-back of a decoded loop body

`DecodeLoopTV.liftRun` reads a decoded machine loop body back as flag-machine instructions
over the names of machine registers and frame words. This module proves the reading sound
for every input: the machine body simulates the flag-machine run of the instructions read
back (`liftRun_sound`), under the correspondence `LCorr`.

`LCorr E base rsp st` relates a machine state to a flag-machine state at the reading state
`st`: the decoded correspondence `DecLsemCorr` at the register map `unlift` (the inverse of
`liftReg` on `liftRegs`) on the names of the live registers (`LiveN`), with the regions of `E`
at the base map `base` and the stack pointer `rsp`, the zero flag when `st.zl` holds; the stack
register holds `rsp`; the name `slot.off` of each live frame word holds the word at
`rsp + off`; and the facts of `st` hold of the machine registers (`Facts`). The separation of
the regions, the frame words of `E.S` and the pointer slots is `LSep`.

## Main results

* `unlift`, `unlift_liftReg` — the machine register of a name read back.
* `LiveN`, `Facts`, `LSep`, `LCorr` — the correspondence.
* `liftInstr_sound`, `liftRun_sound` — an instruction and a body read back are simulated by
  their machine instructions.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTVSound

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTV

/-! ## 1. Names -/

/-- The machine register of a name read back: the register of `liftRegs` that `liftReg`
    sends to it, the name itself otherwise. -/
def unlift (n : String) : String := ((liftRegs.find? fun X => liftReg X == n)).getD n

theorem unlift_liftReg {X : String} (h : X ∈ liftRegs) : unlift (liftReg X) = X := by
  simp only [liftRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

theorem liftReg_inj {X Y : String} (hX : X ∈ liftRegs) (hY : Y ∈ liftRegs)
    (h : liftReg X = liftReg Y) : X = Y := by
  rw [← unlift_liftReg hX, ← unlift_liftReg hY, h]

theorem liftReg_ne_slotName {X : String} (hX : X ∈ liftRegs) (off : Int) :
    liftReg X ≠ slotName off := by
  intro h
  have h' := congrArg (fun s : String => s.toList.head?) h
  simp only [liftRegs, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [slotName] at h' <;> revert h' <;> decide

theorem rsp_not_mem_liftRegs : "%rsp" ∉ liftRegs := by decide

theorem slotName_inj {a c : Int} (h : slotName a = slotName c) : a = c := by
  unfold slotName at h
  have h' : toString a = toString c := by
    have := congrArg String.toList h
    simp only [String.toList_append] at this
    exact String.ext (List.append_cancel_left this)
  exact Int.repr_inj.mp h'

theorem mem_liftRegs_of_live {st : LiftSt} {X : String} (h : st.live X = true) :
    X ∈ liftRegs := by
  simp only [LiftSt.live, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1

theorem not_dead_of_live {st : LiftSt} {X : String} (h : st.live X = true) :
    X ∉ st.dead := by
  intro hm
  simp [LiftSt.live, hm] at h

/-! ## 2. The correspondence -/

/-- The names whose value the flag machine holds as the machine does: the names of the live
    registers of the reading state. -/
def LiveN (st : LiftSt) (n : String) : Prop := ∃ X, st.live X = true ∧ n = liftReg X

/-- The facts of the reading state `st` hold of the machine registers of `sa`, for the base
    map `base` and the loop bound of `E`. -/
structure Facts (E : LiftEnv) (base : String → BitVec 64) (st : LiftSt) (sa : AState) :
    Prop where
  /-- A register of `ptr` holds the base of its region. -/
  ptr : ∀ p ∈ st.ptr, sa.regs p.1 = base p.2
  /-- A register of `imm` holds its constant. -/
  imm : ∀ p ∈ st.imm, sa.regs p.1 = BitVec.ofNat 64 p.2
  /-- A copy holds the value of its source. -/
  cp : ∀ p ∈ st.cp, sa.regs p.1 = sa.regs p.2
  /-- A register of `lo` holds the low word of its product. -/
  lo : ∀ p ∈ st.lo, sa.regs p.1 = sa.regs p.2.1 * sa.regs p.2.2
  /-- A register of `bnd` holds a value below the loop bound plus its offset. -/
  bnd : ∀ p ∈ st.bnd, (sa.regs p.1).toNat < E.nb + p.2

/-- The separation of the frame words of `E.S` from the cells and pointer slots of the
    regions and from one another, with the separation of the regions (`MemSep`). -/
structure LSep (E : LiftEnv) (base : String → BitVec 64) (rsp : BitVec 64) : Prop where
  /-- The regions are separated. -/
  mem : MemSep E.rs base rsp
  /-- A frame word of `E.S` is disjoint from every cell. -/
  cell : ∀ off ∈ E.S, ∀ A j, regK E.rs A j →
    Disjoint8 ((regLay E.rs base).addr A j) (rsp + BitVec.ofInt 64 off)
  /-- Two frame words of `E.S` at distinct offsets are disjoint. -/
  word : ∀ off ∈ E.S, ∀ off' ∈ E.S, off ≠ off' →
    Disjoint8 (rsp + BitVec.ofInt 64 off) (rsp + BitVec.ofInt 64 off')
  /-- A frame word of `E.S` is disjoint from every pointer slot. -/
  slot : ∀ off ∈ E.S, ∀ q a, regFrame E.rs rsp q = some a →
    Disjoint8 (rsp + BitVec.ofInt 64 off) a

/-- **The correspondence at the reading state `st`.** -/
structure LCorr (E : LiftEnv) (base : String → BitVec 64) (rsp : BitVec 64) (st : LiftSt)
    (sa : AState) (b : LstateM) (zf : Bool) : Prop where
  /-- The decoded correspondence on the live names. -/
  corr : DecLsemCorr unlift (LiveN st) (regLay E.rs base) (regFrame E.rs rsp) (regK E.rs)
    (st.zl = true) sa b zf
  /-- The stack register holds `rsp`. -/
  sp : sa.regs "%rsp" = rsp
  /-- The live frame words are frame words of `E.S`. -/
  sliveS : ∀ off ∈ st.slive, off ∈ E.S
  /-- The name of a live frame word holds the word. -/
  slots : ∀ off ∈ st.slive,
    b.reg.getW (slotName off) 64 = some (read64 sa.mem (rsp + BitVec.ofInt 64 off))
  /-- The facts hold. -/
  facts : Facts E base st sa

/-! ## 3. Facts -/

variable {E : LiftEnv} {base : String → BitVec 64} {rsp : BitVec 64}

theorem Facts.kill {st : LiftSt} {sa sa' : AState} (h : Facts E base st sa) (ws : List String)
    (hregs : ∀ r, r ∉ ws → sa'.regs r = sa.regs r) : Facts E base (st.kill ws) sa' where
  ptr p hp := by
    simp [LiftSt.kill] at hp
    rw [hregs _ hp.2]; exact h.ptr p hp.1
  imm p hp := by
    simp [LiftSt.kill] at hp
    rw [hregs _ hp.2]; exact h.imm p hp.1
  cp p hp := by
    simp [LiftSt.kill] at hp
    rw [hregs _ hp.2.1, hregs _ hp.2.2]; exact h.cp p hp.1
  lo p hp := by
    simp [LiftSt.kill] at hp
    rw [hregs _ hp.2.1.1, hregs _ hp.2.1.2, hregs _ hp.2.2]; exact h.lo p hp.1
  bnd p hp := by
    simp [LiftSt.kill] at hp
    rw [hregs _ hp.2]; exact h.bnd p hp.1

theorem Facts.copy {st : LiftSt} {sa : AState} (h : Facts E base st sa) {D X : String}
    (hDX : sa.regs D = sa.regs X) : Facts E base (st.copy D X) sa where
  ptr p hp := by
    simp only [LiftSt.copy, List.mem_append, List.mem_filterMap] at hp
    rcases hp with ⟨q, hq, hq'⟩ | hp
    · split at hq'
      · rename_i hx
        obtain rfl := Option.some.inj hq'
        rw [hDX, ← beq_iff_eq.mp hx]; exact h.ptr q hq
      · cases hq'
    · exact h.ptr p hp
  imm p hp := by
    simp only [LiftSt.copy, List.mem_append, List.mem_filterMap] at hp
    rcases hp with ⟨q, hq, hq'⟩ | hp
    · split at hq'
      · rename_i hx
        obtain rfl := Option.some.inj hq'
        rw [hDX, ← beq_iff_eq.mp hx]; exact h.imm q hq
      · cases hq'
    · exact h.imm p hp
  cp p hp := by
    simp only [LiftSt.copy, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hDX
    · exact h.cp p hp
  lo p hp := by
    simp only [LiftSt.copy, List.mem_append, List.mem_filterMap] at hp
    rcases hp with ⟨q, hq, hq'⟩ | hp
    · split at hq'
      · rename_i hx
        obtain rfl := Option.some.inj hq'
        rw [hDX, ← beq_iff_eq.mp hx]; exact h.lo q hq
      · cases hq'
    · exact h.lo p hp
  bnd p hp := by
    simp only [LiftSt.copy, List.mem_append, List.mem_filterMap] at hp
    rcases hp with ⟨q, hq, hq'⟩ | hp
    · split at hq'
      · rename_i hx
        obtain rfl := Option.some.inj hq'
        show (sa.regs D).toNat < _
        rw [hDX, ← beq_iff_eq.mp hx]; exact h.bnd q hq
      · cases hq'
    · exact h.bnd p hp

theorem Facts.of_regs {st : LiftSt} {sa sa' : AState} (h : Facts E base st sa)
    (hregs : ∀ r, sa'.regs r = sa.regs r) : Facts E base st sa' where
  ptr p hp := by rw [hregs]; exact h.ptr p hp
  imm p hp := by rw [hregs]; exact h.imm p hp
  cp p hp := by rw [hregs, hregs]; exact h.cp p hp
  lo p hp := by rw [hregs, hregs, hregs]; exact h.lo p hp
  bnd p hp := by rw [hregs]; exact h.bnd p hp

/-- The facts after the write of `v` to `D`, those on `D` removed. -/
theorem Facts.write {st : LiftSt} {sa sa' : AState} (h : Facts E base st sa) {D : String}
    {v : BitVec 64} (hregs : ∀ r, sa'.regs r = if r = D then v else sa.regs r) :
    Facts E base (st.kill [D]) sa' :=
  h.kill [D] fun r hr => by rw [hregs, if_neg (fun e => hr (List.mem_singleton.mpr e))]

/-- The facts after the write of `v` to `D`, those on `D` removed, the zero flag untracked. -/
theorem Facts.writeZ {st : LiftSt} {sa sa' : AState} (h : Facts E base st sa) {D : String}
    {v : BitVec 64} (hregs : ∀ r, sa'.regs r = if r = D then v else sa.regs r) :
    Facts E base { st.kill [D] with zl := false } sa' := by
  have hk := h.write hregs
  exact ⟨hk.ptr, hk.imm, hk.cp, hk.lo, hk.bnd⟩

theorem mem_of_lookup {α : Type} {l : List (String × α)} {k : String} {v : α}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i he
      obtain rfl := Option.some.inj h
      exact List.mem_cons.mpr (Or.inl (by rw [beq_iff_eq.mp he]))
    · exact List.mem_cons_of_mem _ (ih h)

/-- The facts after the addition of the constant `n` to `D`. -/
theorem Facts.addConst {st : LiftSt} {sa sa' : AState} (h : Facts E base st sa) {D : String}
    {n : Nat} (hregs : ∀ r, sa'.regs r = if r = D then sa.regs D + BitVec.ofNat 64 n
      else sa.regs r) :
    Facts E base (st.addConst E D n) sa' := by
  have hk := h.write hregs
  unfold LiftSt.addConst
  split
  · rename_i δ hδ
    split
    · rename_i hle
      refine { hk with bnd := fun p hp => ?_ }
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · have hb := h.bnd (D, δ) (mem_of_lookup hδ)
        simp only [hregs, if_true, BitVec.toNat_add, BitVec.toNat_ofNat] at hb ⊢
        have hn : n < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
        omega
      · exact hk.bnd p hp
    · exact ⟨hk.ptr, hk.imm, hk.cp, hk.lo, hk.bnd⟩
  · exact ⟨hk.ptr, hk.imm, hk.cp, hk.lo, hk.bnd⟩

/-! ## 4. Steps of the correspondence -/

/-- **A register write.** The machine writes `v` to the register `D` of `liftRegs` and the
    flag machine writes `v` to its name, memory unchanged; the live registers after are `D`
    and live registers before, the live frame words after are live before. -/
theorem LCorr.write {st st' : LiftSt} {sa sa' : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) {D : String} (hD : D ∈ liftRegs) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = D then v else sa.regs r) (hmem : sa'.mem = sa.mem)
    (hlive : ∀ X, st'.live X = true → X = D ∨ st.live X = true)
    (hzl : st'.zl = true → sa'.flags.zf.getD false = zf)
    (hslive : ∀ off ∈ st'.slive, off ∈ st.slive) (hfacts : Facts E base st' sa') :
    LCorr E base rsp st' sa' ((b.setReg (liftReg D) v).nextPc) zf where
  corr := by
    refine h.corr.write (liftReg D) v sa' (fun r => by rw [hregs, unlift_liftReg hD]) hmem
      ?_ hzl
    rintro r ⟨X, hX, rfl⟩
    by_cases hXD : X = D
    · exact Or.inl (by rw [hXD])
    · rcases hlive X hX with hXD' | hX'
      · exact absurd hXD' hXD
      · refine Or.inr ⟨⟨X, hX', rfl⟩, ?_⟩
        rw [unlift_liftReg (mem_liftRegs_of_live hX'), unlift_liftReg hD]
        exact hXD
  sp := by
    have hne : ("%rsp" : String) ≠ D := fun e => rsp_not_mem_liftRegs (by rw [e]; exact hD)
    rw [hregs, if_neg hne, h.sp]
  sliveS off ho := h.sliveS off (hslive off ho)
  slots off ho := by
    rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_other _ _ _ _ _ (fun e => liftReg_ne_slotName hD off e.symm), hmem]
    exact h.slots off (hslive off ho)
  facts := hfacts

/-- The correspondence does not read the flag machine's carry and overflow flags. -/
theorem LCorr.setFlags {st : LiftSt} {sa : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) (c o : Bool) :
    LCorr E base rsp st sa { b with cf := c, of := o } zf where
  corr := DecodeCarry.DecLsemCorr.setFlags h.corr c o
  sp := h.sp
  sliveS := h.sliveS
  slots := h.slots
  facts := h.facts

/-- The correspondence after `withALUFlags`. -/
theorem LCorr.withALUFlags {st : LiftSt} {sa : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) (i : LinstrRM) (s0 : LstateM) :
    LCorr E base rsp st sa (withALUFlags i s0 b) zf := by
  obtain ⟨c, o, he⟩ := withALUFlags_eq i s0 b
  rw [he]
  exact h.setFlags c o

/-- The value of a live register's name. -/
theorem LCorr.getW {st : LiftSt} {sa : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) {X : String} (hX : st.live X = true) :
    b.reg.getW (liftReg X) 64 = some (sa.regs X) := by
  have := h.corr.regs (liftReg X) ⟨X, hX, rfl⟩
  rwa [unlift_liftReg (mem_liftRegs_of_live hX)] at this

theorem live_kill {st : LiftSt} {ws : List String} {X : String}
    (h : (st.kill ws).live X = true) : X ∈ ws ∨ st.live X = true := by
  by_cases hX : X ∈ ws
  · exact Or.inl hX
  · refine Or.inr ?_
    simp only [LiftSt.live, LiftSt.kill, Bool.and_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at h ⊢
    refine ⟨h.1, ?_⟩
    simpa [hX] using h.2

/-! ## 5. Machine steps -/

theorem evalInstrA_mov_reg (sa : AState) (D X r : String) :
    (evalInstrA sa (.mov D (.reg X))).regs r = if r = D then sa.regs X else sa.regs r := by
  by_cases hr : r = D <;> simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_MOV]

theorem evalInstrA_mov_flags (sa : AState) (D : String) (s : JOperand) :
    (evalInstrA sa (.mov D s)).flags = sa.flags := by
  simp [evalInstrA, evalInstr, JState.setReg, AState.view]

theorem evalInstrA_mov_imm (sa : AState) (D r : String) (n : Nat) :
    (evalInstrA sa (.mov D (.imm n))).regs r = if r = D then BitVec.ofNat 64 n else sa.regs r := by
  by_cases hr : r = D <;> simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_MOV,
    JOperand.eval]

theorem evalInstrA_add_reg (sa : AState) (D Y r : String) :
    (evalInstrA sa (.add D (.reg Y))).regs r
      = if r = D then sa.regs D + sa.regs Y else sa.regs r := by
  by_cases hr : r = D <;>
    simp [evalInstrA, evalInstr, JState.writeB5W, AState.view, hr, x86_ADD, rflags_of_aluop]

theorem evalInstrA_loadMem (sa : AState) (S B r : String) (off : Int) :
    (evalInstrA sa (.loadMem S B off)).regs r
      = if r = S then read64 sa.mem (sa.regs B + BitVec.ofInt 64 off) else sa.regs r := by
  by_cases hr : r = S <;> simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_MOV]

theorem evalInstrA_loadMem_flags (sa : AState) (S B : String) (off : Int) :
    (evalInstrA sa (.loadMem S B off)).flags = sa.flags := by
  simp [evalInstrA, evalInstr, JState.setReg, AState.view]

theorem evalInstrA_storeMem (sa : AState) (B X : String) (off : Int) :
    (evalInstrA sa (.storeMem B off (.reg X))).regs = sa.regs
      ∧ (evalInstrA sa (.storeMem B off (.reg X))).flags = sa.flags
      ∧ (evalInstrA sa (.storeMem B off (.reg X))).mem
        = write64 sa.mem (sa.regs B + BitVec.ofInt 64 off) (sa.regs X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [evalInstrA, evalInstr, JState.store, AState.view, writeAddr, writeVal, JOperand.eval]

theorem evalInstrA_cmpMem (sa : AState) (A B : String) (off : Int) :
    (evalInstrA sa (.cmpMem A B off)).regs = sa.regs
      ∧ (evalInstrA sa (.cmpMem A B off)).mem = sa.mem
      ∧ (evalInstrA sa (.cmpMem A B off)).flags.zf.getD false
        = (sa.regs A == read64 sa.mem (sa.regs B + BitVec.ofInt 64 off)) := by
  refine ⟨?_, rfl, ?_⟩
  · simp [evalInstrA, evalInstr, JState.writeB5, AState.view]
  · show (some (ZF_of_word (sa.regs A - read64 sa.mem (sa.regs B + BitVec.ofInt 64 off)))).getD
      false = _
    rw [ZF_of_word_sub]; rfl

theorem evalInstrA_cmp_regs (sa : AState) (A : String) (o : JOperand) :
    (evalInstrA sa (.cmp A o)).regs = sa.regs := by
  simp [evalInstrA, evalInstr, JState.writeB5, AState.view]

theorem evalInstrA_cmp_reg_zf (sa : AState) (A X : String) :
    (evalInstrA sa (.cmp A (.reg X))).flags.zf.getD false = (sa.regs A == sa.regs X) := by
  show (some (ZF_of_word (sa.regs A - sa.regs X))).getD false = _
  rw [ZF_of_word_sub]; rfl

theorem evalInstrA_mulx (sa : AState) (H Lo S C r : String) :
    (evalInstrA sa (.mulx H Lo (.reg S) (.reg C))).regs r
      = if r = H then (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).2
        else if r = Lo then (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).1 else sa.regs r := by
  by_cases h1 : r = H <;> by_cases h2 : r = Lo <;>
    simp [evalInstrA, evalInstr, AState.view, JState.setReg, h1, h2]

/-! ## 6. The classes -/

/-- **A register copy.** -/
theorem decSim_lift_movReg {st : LiftSt} {D X : String} (hD : D ∈ liftRegs)
    (hX : st.live X = true) (hXD : X ≠ D) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp ((st.kill [D]).copy D X))
      [opI "MOV" D [.reg (liftReg X)]] [.mov D (.reg X)] := by
  refine DecSim.single fun sa b zf h => ⟨_, zf, fstepF_movRI _ _ b zf _ (h.getW hX), ?_⟩
  have hregs := evalInstrA_mov_reg sa D X
  have hfl := evalInstrA_mov_flags sa D (.reg X)
  refine h.write hD _ hregs rfl ?_ ?_ (fun off ho => ho) ?_
  · intro Y hY
    rcases live_kill (ws := [D]) (st := st) hY with hY | hY
    · exact Or.inl (List.mem_singleton.mp hY)
    · exact Or.inr hY
  · intro hz; rw [hfl]; exact h.corr.zfEq hz
  · refine (h.facts.kill [D] fun r hr => ?_).copy ?_
    · rw [hregs, if_neg (fun e => hr (List.mem_singleton.mpr e))]
    · rw [hregs, hregs, if_pos rfl, if_neg hXD]

/-- **A two-address operation on registers.** `opn D, D, Y` against `mk %Y, %D`, for the
    operation `f` of both machines, to a reading state `st'` whose live registers are `D` and
    live registers of `st`, whose zero flag is untracked, whose live frame words are live in
    `st` and whose facts follow from those of `st` after the write. -/
theorem decSim_lift_binReg (opn mn : String) (hstrip : stripWidthTag opn = mn)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : mn ≠ "MULXHI")
    (hcarry : mn ≠ "ADC" ∧ mn ≠ "SBB" ∧ mn ≠ "ADCX" ∧ mn ≠ "ADOX")
    (hmov : mn ≠ "MOV")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 mn [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    {st st' : LiftSt} {D Y : String} (hD : st.live D = true) (hY : st.live Y = true)
    (hlive : ∀ X, st'.live X = true → X = D ∨ st.live X = true) (hzl : st'.zl = false)
    (hslive : ∀ off ∈ st'.slive, off ∈ st.slive)
    (hfacts : ∀ sa sa' : AState, Facts E base st sa →
      (∀ r, sa'.regs r = if r = D then f (sa.regs D) (sa.regs Y) else sa.regs r) →
      Facts E base st' sa') :
    DecSim (LCorr E base rsp st) (LCorr E base rsp st')
      [binRegI opn (liftReg D) (liftReg D) (liftReg Y)] [mk D (.reg Y)] := by
  refine DecSim.single fun sa b zf h => ?_
  have hstep := fstepF_binRegI opn mn (liftReg D) (liftReg D) (liftReg Y) hstrip hcmp hmul
    hcarry hmov b zf (sa.regs D) (h.getW hD)
  rw [h.getW hY, Option.bind_some, hf, Option.map_some] at hstep
  refine ⟨_, zf, hstep, LCorr.withALUFlags ?_ _ _⟩
  exact h.write (mem_liftRegs_of_live hD) _ (hmk sa D Y) (hmkm sa D Y) hlive
    (fun hz => by rw [hzl] at hz; cases hz) hslive (hfacts sa _ h.facts (hmk sa D Y))

theorem live_killZ {st : LiftSt} {D X : String} (h : { st.kill [D] with zl := false }.live X = true) :
    X = D ∨ st.live X = true := by
  rcases live_kill (ws := [D]) (st := st) h with h | h
  · exact Or.inl (List.mem_singleton.mp h)
  · exact Or.inr h

theorem addConst_live {st : LiftSt} {D X : String} {n : Nat}
    (h : (st.addConst E D n).live X = true) : X = D ∨ st.live X = true := by
  unfold LiftSt.addConst at h
  split at h
  · split at h
    · exact live_killZ (D := D) (by simpa [LiftSt.live] using h)
    · exact live_killZ h
  · exact live_killZ h

theorem addConst_zl {st : LiftSt} {D : String} {n : Nat} : (st.addConst E D n).zl = false := by
  unfold LiftSt.addConst
  split
  · split <;> rfl
  · rfl

theorem addConst_slive {st : LiftSt} {D : String} {n : Nat} :
    (st.addConst E D n).slive = st.slive := by
  unfold LiftSt.addConst
  split
  · split <;> rfl
  · rfl

/-- The lifted `add` of a register. -/
theorem decSim_lift_add {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp
        (match st.immOf Y with
          | some n => if Y == D then { st.kill [D] with zl := false } else st.addConst E D n
          | none => { st.kill [D] with zl := false }))
      [binRegI (withWidthTag 64 "ADD") (liftReg D) (liftReg D) (liftReg Y)] [.add D (.reg Y)] := by
  refine decSim_lift_binReg _ "ADD" (by decide +kernel) (by decide +kernel) (by decide)
    (by decide) (by decide) (· + ·) (fun _ _ => rfl) JInstr.add (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) hD hY ?_ ?_ ?_ ?_
  · intro X hX
    split at hX
    · split at hX
      · exact live_killZ hX
      · exact addConst_live hX
    · exact live_killZ hX
  · split
    · split
      · rfl
      · exact addConst_zl
    · rfl
  · intro off ho
    split at ho
    · split at ho
      · exact ho
      · rwa [addConst_slive] at ho
    · exact ho
  · intro sa sa' hf hregs
    split
    · rename_i n hn
      split
      · exact hf.writeZ hregs
      · have hYv : sa.regs Y = BitVec.ofNat 64 n := hf.imm (Y, n) (mem_of_lookup hn)
        refine hf.addConst fun r => ?_
        rw [hregs, hYv]
    · exact hf.writeZ hregs

/-- A two-address operation on registers after which the facts on `D` are dropped. -/
theorem decSim_lift_binKill (mn : String) (hcmp : withWidthTag 64 mn ≠ withWidthTag 64 "CMP")
    (hstrip : stripWidthTag (withWidthTag 64 mn) = mn) (hmul : mn ≠ "MULXHI")
    (hcarry : mn ≠ "ADC" ∧ mn ≠ "SBB" ∧ mn ≠ "ADCX" ∧ mn ≠ "ADOX") (hmov : mn ≠ "MOV")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 mn [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    {st : LiftSt} {D Y : String} (hD : st.live D = true) (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [binRegI (withWidthTag 64 mn) (liftReg D) (liftReg D) (liftReg Y)] [mk D (.reg Y)] :=
  decSim_lift_binReg _ mn hstrip hcmp hmul hcarry hmov f hf mk hmk hmkm hD hY
    (fun _ hX => live_killZ hX) rfl (fun _ ho => ho) (fun _ _ hf hregs => hf.writeZ hregs)

theorem decSim_lift_sub {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [binRegI (withWidthTag 64 "SUB") (liftReg D) (liftReg D) (liftReg Y)] [.sub D (.reg Y)] :=
  decSim_lift_binKill "SUB" (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (· - ·) (fun _ _ => rfl) JInstr.sub (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hD hY

theorem decSim_lift_xor {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [binRegI (withWidthTag 64 "XOR") (liftReg D) (liftReg D) (liftReg Y)] [.xor_ D (.reg Y)] :=
  decSim_lift_binKill "XOR" (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (· ^^^ ·) (fun _ _ => rfl) JInstr.xor_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    hD hY

theorem decSim_lift_or {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [binRegI (withWidthTag 64 "OR") (liftReg D) (liftReg D) (liftReg Y)] [.or_ D (.reg Y)] :=
  decSim_lift_binKill "OR" (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (· ||| ·) (fun _ _ => rfl) JInstr.or_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    hD hY

/-- The lifted `and` of a register: with a register holding the all-ones word, the value of
    `D` and its facts are kept. -/
theorem decSim_lift_and {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp
        (if Y != D && st.immOf Y == some (2 ^ 64 - 1) then { st with zl := false }
          else { st.kill [D] with zl := false }))
      [binRegI (withWidthTag 64 "AND") (liftReg D) (liftReg D) (liftReg Y)] [.and_ D (.reg Y)] := by
  refine decSim_lift_binReg _ "AND" (by decide +kernel) (by decide +kernel) (by decide)
    (by decide) (by decide) (· &&& ·) (fun _ _ => rfl) JInstr.and_ (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) hD hY ?_ ?_ ?_ ?_
  · intro X hX
    split at hX
    · exact Or.inr hX
    · exact live_killZ hX
  · split <;> rfl
  · intro off ho
    split at ho <;> exact ho
  · intro sa sa' hf hregs
    split
    · rename_i hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      have hYv : sa.regs Y = BitVec.ofNat 64 (2 ^ 64 - 1) := hf.imm (Y, _) (mem_of_lookup hc.2)
      have hf' := hf.of_regs (sa' := sa') fun r => by
        rw [hregs]
        split
        · rename_i hr
          subst hr
          have h1 : BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 := by decide
          rw [hYv, h1]
          exact BitVec.and_allOnes
        · rfl
      exact ⟨hf'.ptr, hf'.imm, hf'.cp, hf'.lo, hf'.bnd⟩
    · exact hf.writeZ hregs

/-- The lifted `imul` of a register: `D` holds the low word of the product of `X` and `Y`
    when it held a copy of `X`. -/
theorem decSim_lift_imul {st : LiftSt} {D Y : String} (hD : st.live D = true)
    (hY : st.live Y = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp
        (let new := if Y == D then [] else
            (st.cp.filter fun p => p.1 == D && p.2 != D).map fun p => (D, p.2, Y)
          let st' := { st.kill [D] with zl := false }
          { st' with lo := new ++ st'.lo }))
      [binRegI (withWidthTag 64 "MUL") (liftReg D) (liftReg D) (liftReg Y)] [.imul D (.reg Y)] := by
  refine decSim_lift_binReg _ "MUL" (by decide +kernel) (by decide +kernel) (by decide)
    (by decide) (by decide) (· * ·) (fun _ _ => rfl) JInstr.imul (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) hD hY ?_ rfl (fun _ ho => ho) ?_
  · intro X hX
    exact live_killZ hX
  · intro sa sa' hf hregs
    have hk := hf.writeZ hregs
    refine ⟨hk.ptr, hk.imm, hk.cp, fun p hp => ?_, hk.bnd⟩
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · split at hp
      · cases hp
      · rename_i hYD
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
          ne_eq] at hp
        obtain ⟨q, ⟨hq, hq1, hq2⟩, rfl⟩ := hp
        have hYD' : Y ≠ D := fun e => hYD (by rw [e]; exact beq_self_eq_true D)
        have hc := hf.cp q hq
        rw [hq1] at hc
        show sa'.regs D = sa'.regs q.2 * sa'.regs Y
        rw [hregs, hregs, hregs, if_pos rfl, if_neg hq2, if_neg hYD', hc]
    · exact hk.lo p hp

/-- **A self-copy.** -/
theorem decSim_lift_movSelf {st : LiftSt} {D : String} (hD : st.live D = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp st)
      [opI "MOV" D [.reg (liftReg D)]] [.mov D (.reg D)] := by
  refine DecSim.single fun sa b zf h => ⟨_, zf, fstepF_movRI _ _ b zf _ (h.getW hD), ?_⟩
  have hregs := evalInstrA_mov_reg sa D D
  refine h.write (mem_liftRegs_of_live hD) _ hregs rfl (fun _ hX => Or.inr hX)
    (fun hz => by rw [evalInstrA_mov_flags]; exact h.corr.zfEq hz) (fun _ ho => ho)
    (h.facts.of_regs fun r => by rw [hregs]; split <;> simp_all)

/-- **An immediate move.** -/
theorem decSim_lift_movImm {st : LiftSt} {D : String} (hD : D ∈ liftRegs) (n : Nat) :
    DecSim (LCorr E base rsp st)
      (LCorr E base rsp { st.kill [D] with imm := (D, n) :: (st.kill [D]).imm })
      [opI "MOV" D [.imm n]] [.mov D (.imm n)] := by
  refine DecSim.single fun sa b zf h => ⟨_, zf, fstepF_movII _ _ b zf, ?_⟩
  have hregs := fun r => evalInstrA_mov_imm sa D r n
  refine h.write hD _ hregs rfl ?_
    (fun hz => by rw [evalInstrA_mov_flags]; exact h.corr.zfEq hz) (fun _ ho => ho) ?_
  · intro X hX
    rcases live_kill (ws := [D]) (st := st) hX with hX | hX
    · exact Or.inl (List.mem_singleton.mp hX)
    · exact Or.inr hX
  · have hk := h.facts.write hregs
    refine ⟨hk.ptr, fun p hp => ?_, hk.cp, hk.lo, hk.bnd⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · show (evalInstrA sa (.mov D (.imm n))).regs D = _
      rw [hregs, if_pos rfl]
    · exact hk.imm p hp

/-- **The addition of an immediate.** -/
theorem decSim_lift_addImm {st : LiftSt} {D : String} (hD : st.live D = true) (k : Nat) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp (st.addConst E D k))
      [addImmI (liftReg D) (liftReg D) k] [.add D (.imm k)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_addImmI _ _ k b zf _ (h.getW hD), LCorr.withALUFlags ?_ _ _⟩
  have hregs : ∀ r, (evalInstrA sa (.add D (.imm k))).regs r
      = if r = D then sa.regs D + BitVec.ofNat 64 k else sa.regs r := fun r => rfl
  exact h.write (mem_liftRegs_of_live hD) _ hregs rfl (fun _ hX => addConst_live hX)
    (fun hz => by rw [addConst_zl] at hz; cases hz) (fun _ ho => by rwa [addConst_slive] at ho)
    (h.facts.addConst hregs)

/-- **The subtraction of an immediate.** -/
theorem decSim_lift_subImm {st : LiftSt} {D : String} (hD : st.live D = true) (k : Nat) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [subImmI (liftReg D) (liftReg D) k] [.sub D (.imm k)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_subImmI _ _ k b zf _ (h.getW hD), LCorr.withALUFlags ?_ _ _⟩
  have hregs : ∀ r, (evalInstrA sa (.sub D (.imm k))).regs r
      = if r = D then sa.regs D - BitVec.ofNat 64 k else sa.regs r := fun r => rfl
  exact h.write (mem_liftRegs_of_live hD) _ hregs rfl (fun _ hX => live_killZ hX)
    (fun hz => by cases hz) (fun _ ho => ho) (h.facts.writeZ hregs)

/-- **A right shift by an immediate count.** -/
theorem decSim_lift_shr {st : LiftSt} {D : String} (hD : st.live D = true) {k : Nat}
    (hk0 : k ≠ 0) (hk : k < 64) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [immShiftI "SHR" (liftReg D) (liftReg D) k] [.shr D (.imm k)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_shrImmI _ _ k hk b zf _ (h.getW hD), ?_⟩
  have hregs : ∀ r, (evalInstrA sa (.shr D (.imm k))).regs r
      = if r = D then sa.regs D >>> k else sa.regs r := fun r => by
    show (if r = D then (x86_SHR (sa.regs D) (BitVec.ofNat 64 k)).word else sa.regs r) = _
    rw [x86_SHR_word_imm _ k hk0 hk]
  exact h.write (mem_liftRegs_of_live hD) _ hregs rfl (fun _ hX => live_killZ hX)
    (fun hz => by cases hz) (fun _ ho => ho) (h.facts.writeZ hregs)

/-- **A left shift by an immediate count.** -/
theorem decSim_lift_shl {st : LiftSt} {D : String} (hD : st.live D = true) {k : Nat}
    (hk0 : k ≠ 0) (hk : k < 64) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st.kill [D] with zl := false })
      [immShiftI "SHL" (liftReg D) (liftReg D) k] [.shl D (.imm k)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, DecodeGenSim.fstepF_shlImmI _ _ k hk b zf _ (h.getW hD), ?_⟩
  have hregs : ∀ r, (evalInstrA sa (.shl D (.imm k))).regs r
      = if r = D then sa.regs D <<< k else sa.regs r := fun r => by
    show (if r = D then (x86_SHL (sa.regs D) (BitVec.ofNat 64 k)).word else sa.regs r) = _
    rw [DecodeGenSim.x86_SHL_word_imm _ k hk0 hk]
  exact h.write (mem_liftRegs_of_live hD) _ hregs rfl (fun _ hX => live_killZ hX)
    (fun hz => by cases hz) (fun _ ho => ho) (h.facts.writeZ hregs)

/-- A compare: the flag machine moves the program counter and sets the zero flag to the
    machine's. -/
theorem LCorr.cmp {st : LiftSt} {sa sa' : AState} {b : LstateM} {zf zf' : Bool}
    (h : LCorr E base rsp st sa b zf) (hregs : sa'.regs = sa.regs) (hmem : sa'.mem = sa.mem)
    (hz : sa'.flags.zf.getD false = zf') :
    LCorr E base rsp { st with zl := true } sa' b.nextPc zf' where
  corr := h.corr.flagOnly sa' zf' hregs hmem (fun _ => hz)
  sp := by rw [hregs]; exact h.sp
  sliveS := h.sliveS
  slots off ho := by
    rw [LstateM.reg_nextPc, LstateN.getW_nextPc, hmem]; exact h.slots off ho
  facts := by
    have hf := h.facts.of_regs (sa' := sa') fun r => by rw [hregs]
    exact ⟨hf.ptr, hf.imm, hf.cp, hf.lo, hf.bnd⟩

/-- **A machine-only write.** The machine writes registers of `ws` other than the stack
    register, memory and flags unchanged; no live register after is written, and the zero
    flag and live frame words are kept. -/
theorem LCorr.mach {st st' : LiftSt} {sa sa' : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) (ws : List String)
    (hregs : ∀ r, r ∉ ws → sa'.regs r = sa.regs r) (hmem : sa'.mem = sa.mem)
    (hfl : sa'.flags = sa.flags) (hrsp : "%rsp" ∉ ws)
    (hlive : ∀ X, st'.live X = true → st.live X = true ∧ X ∉ ws) (hzl : st'.zl = st.zl)
    (hslive : ∀ off ∈ st'.slive, off ∈ st.slive) (hfacts : Facts E base st' sa') :
    LCorr E base rsp st' sa' b zf where
  corr :=
    { regs := by
        rintro r ⟨X, hX, rfl⟩
        obtain ⟨hX', hXw⟩ := hlive X hX
        rw [unlift_liftReg (mem_liftRegs_of_live hX), hregs X hXw]
        have := h.corr.regs (liftReg X) ⟨X, hX', rfl⟩
        rwa [unlift_liftReg (mem_liftRegs_of_live hX)] at this
      zfEq := fun hz => by rw [hfl]; exact h.corr.zfEq (by rw [← hzl]; exact hz)
      cells := fun A j hk => by rw [hmem]; exact h.corr.cells A j hk
      slots := fun A q hq => by rw [hmem]; exact h.corr.slots A q hq }
  sp := by rw [hregs _ hrsp]; exact h.sp
  sliveS off ho := h.sliveS off (hslive off ho)
  slots off ho := by rw [hmem]; exact h.slots off (hslive off ho)
  facts := hfacts

theorem live_killDead {st : LiftSt} {D X : String}
    (h : (let st' := st.kill [D]; { st' with dead := D :: st'.dead }).live X = true) :
    st.live X = true ∧ X ∉ [D] := by
  have hXD : X ≠ D := by
    rintro rfl
    simp [LiftSt.live] at h
  have h' : (st.kill [D]).live X = true := by
    simp only [LiftSt.live, Bool.and_eq_true, List.contains_iff_mem] at h ⊢
    refine ⟨h.1, ?_⟩
    simpa [hXD] using h.2
  rcases live_kill h' with h'' | h''
  · exact absurd (List.mem_singleton.mp h'') hXD
  · exact ⟨h'', fun hm => hXD (List.mem_singleton.mp hm)⟩

/-- **A copy of a register whose name does not hold its value.** -/
theorem decSim_lift_movDead {st : LiftSt} {D X : String} (hD : D ∈ liftRegs) :
    DecSim (LCorr E base rsp st)
      (LCorr E base rsp (let st' := st.kill [D]; { st' with dead := D :: st'.dead }))
      [] [.mov D (.reg X)] := by
  refine DecSim.machOnly fun sa b zf h => ?_
  have hregs := evalInstrA_mov_reg sa D X
  refine h.mach [D] (fun r hr => by rw [hregs, if_neg (fun e => hr (List.mem_singleton.mpr e))])
    rfl (evalInstrA_mov_flags sa D _)
    (fun e => rsp_not_mem_liftRegs (by rw [List.mem_singleton.mp e]; exact hD))
    (fun _ hX => live_killDead hX) rfl (fun _ ho => ho) ?_
  have hk := h.facts.write hregs
  exact ⟨hk.ptr, hk.imm, hk.cp, hk.lo, hk.bnd⟩

/-- **The reload of the base of a region from its pointer slot.** -/
theorem decSim_lift_reload {st : LiftSt} {S : String} {g : Region} (hS : S ∈ liftRegs)
    (hg : regFind E.rs g.name = some g) :
    DecSim (LCorr E base rsp st)
      (LCorr E base rsp (let st' := st.kill [S];
        { st' with ptr := (S, g.name) :: st'.ptr, dead := S :: st'.dead }))
      [] [.loadMem S "%rsp" g.off] := by
  refine DecSim.machOnly fun sa b zf h => ?_
  have hregs := fun r => evalInstrA_loadMem sa S "%rsp" r g.off
  have hval : read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 g.off) = base g.name := by
    obtain ⟨a, ha, hr⟩ := h.corr.slots g.name g.name (by simp [regLay, hg])
    simp only [regFrame, hg, Option.map_some, Option.some.injEq] at ha
    rw [h.sp, ha]; exact hr
  refine h.mach [S] (fun r hr => by rw [hregs, if_neg (fun e => hr (List.mem_singleton.mpr e))])
    rfl rfl (fun e => rsp_not_mem_liftRegs (by rw [List.mem_singleton.mp e]; exact hS))
    (fun X hX => live_killDead (D := S) (by simpa [LiftSt.live] using hX)) rfl
    (fun _ ho => ho) ?_
  have hk := h.facts.write hregs
  refine ⟨fun p hp => ?_, hk.imm, hk.cp, hk.lo, hk.bnd⟩
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · show (evalInstrA sa (.loadMem S "%rsp" g.off)).regs S = _
    rw [hregs, if_pos rfl, hval]
  · exact hk.ptr p hp

/-- **The load of a live frame word.** -/
theorem decSim_lift_slotLoad {st : LiftSt} {S : String} {off : Int} (hS : S ∈ liftRegs)
    (ho : off ∈ st.slive) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp (st.kill [S]))
      [opI "MOV" S [.reg (slotName off)]] [.loadMem S "%rsp" off] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_movRI _ _ b zf _ (h.slots off ho), ?_⟩
  have hregs : ∀ r, (evalInstrA sa (.loadMem S "%rsp" off)).regs r
      = if r = S then read64 sa.mem (rsp + BitVec.ofInt 64 off) else sa.regs r := fun r => by
    rw [evalInstrA_loadMem, h.sp]
  refine h.write hS _ hregs rfl ?_
    (fun hz => by rw [evalInstrA_loadMem_flags]; exact h.corr.zfEq hz) (fun _ ho => ho)
    (h.facts.write hregs)
  intro X hX
  rcases live_kill (ws := [S]) (st := st) hX with hX | hX
  · exact Or.inl (List.mem_singleton.mp hX)
  · exact Or.inr hX

/-- **The store of a register to a frame word of `E.S`.** -/
theorem decSim_lift_slotStore (hsep : LSep E base rsp) {st : LiftSt} {X : String} {off : Int}
    (hX : st.live X = true) (hoS : off ∈ E.S) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st with slive := off :: st.slive })
      [(.Lopn [.reg (slotName off)] (withWidthTag 64 "MOV") [.reg (liftReg X)], .reg none)]
      [.storeMem "%rsp" off (.reg X)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_movRI (slotName off) (liftReg X) b zf _ (h.getW hX), ?_⟩
  obtain ⟨hregs, hfl, hmem⟩ := evalInstrA_storeMem sa "%rsp" X off
  rw [h.sp] at hmem
  have hXL := mem_liftRegs_of_live hX
  have hne : ∀ Y ∈ liftRegs, liftReg Y ≠ slotName off := fun Y hY => liftReg_ne_slotName hY off
  refine
    { corr :=
        { regs := ?_
          zfEq := fun hz => by rw [hfl]; exact h.corr.zfEq hz
          cells := ?_
          slots := ?_ }
      sp := by rw [hregs]; exact h.sp
      sliveS := ?_
      slots := ?_
      facts := ⟨fun p hp => by rw [hregs]; exact h.facts.ptr p hp,
        fun p hp => by rw [hregs]; exact h.facts.imm p hp,
        fun p hp => by rw [hregs]; exact h.facts.cp p hp,
        fun p hp => by rw [hregs]; exact h.facts.lo p hp,
        fun p hp => by rw [hregs]; exact h.facts.bnd p hp⟩ }
  · rintro r ⟨Y, hY, rfl⟩
    rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_other _ _ _ _ _ (hne Y (mem_liftRegs_of_live hY)), hregs]
    exact h.corr.regs (liftReg Y) ⟨Y, hY, rfl⟩
  · intro A j hk
    obtain ⟨hj, arr, ha, hr⟩ := h.corr.cells A j hk
    refine ⟨hj, arr, by simpa using ha, ?_⟩
    rw [hmem, read64_write64_of_disjoint _ _ _ _ (hsep.cell off hoS A j hk).symm]
    exact hr
  · intro A q hq
    obtain ⟨a, ha, hr⟩ := h.corr.slots A q hq
    refine ⟨a, ha, ?_⟩
    rw [hmem, read64_write64_of_disjoint _ _ _ _ (hsep.slot off hoS q a ha)]
    exact hr
  · intro o ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact hoS
    · exact h.sliveS o ho
  · intro o ho
    simp only [List.mem_cons] at ho
    rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc, hmem]
    by_cases he : o = off
    · subst he
      rw [LstateN.getW_setReg_same, read64_write64_same]
    · rcases ho with rfl | ho
      · exact absurd rfl he
      · rw [LstateN.getW_setReg_other _ _ _ _ _ (fun e => he (slotName_inj e)),
          read64_write64_of_disjoint _ _ _ _ (hsep.word off hoS o (h.sliveS o ho) (Ne.symm he))]
        exact h.slots o ho

/-- **A compare with a live frame word.** -/
theorem decSim_lift_cmpMem {st : LiftSt} {A : String} {off : Int} (hA : st.live A = true)
    (ho : off ∈ st.slive) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st with zl := true })
      [cmpRI (liftReg A) (.reg (slotName off))] [.cmpMem A "%rsp" off] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, _, fstepF_cmpRI _ _ b zf _ _ (h.getW hA) (h.slots off ho), ?_⟩
  obtain ⟨hregs, hmem, hz⟩ := evalInstrA_cmpMem sa A "%rsp" off
  rw [h.sp] at hz
  exact h.cmp hregs hmem hz

/-- The index of a live register with an index fact `(X, δ)`, `nb + δ` at most the length
    of the region `A`, selects a cell of `A`. -/
theorem LCorr.idx {st : LiftSt} {sa : AState} {b : LstateM} {zf : Bool}
    (h : LCorr E base rsp st sa b zf) {X A : String} {δ : Nat} (hδ : st.bndOf X = some δ)
    (hle : E.nb + δ ≤ regLen E.rs A) : regK E.rs A (sa.regs X).toNat := by
  have : (sa.regs X).toNat < E.nb + δ := h.facts.bnd (X, δ) (mem_of_lookup hδ)
  show _ < _
  omega

/-- **An indexed load through a register holding the base of a region.** -/
theorem decSim_lift_loadIdx {st : LiftSt} {D B X A : String} {δ : Nat} (hD : D ∈ liftRegs)
    (hX : st.live X = true) (hB : st.ptr.lookup B = some A) (hδ : st.bndOf X = some δ)
    (hle : E.nb + δ ≤ regLen E.rs A) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp (st.kill [D]))
      [(.Lopn [.reg (liftReg D)] "LOADIDX" [.arrIdx A (liftReg X) 8], .load 64 (regLen E.rs A))]
      [.loadMemIdx D B X 8] := by
  refine DecSim.single fun sa b zf h => ?_
  have hK := h.idx hδ hle
  obtain ⟨_, arr, harr, hcell⟩ := h.corr.cells A _ hK
  have hBv : sa.regs B = (regLay E.rs base).base A := h.facts.ptr (B, A) (mem_of_lookup hB)
  refine ⟨(b.setReg (liftReg D) (stackGet arr (sa.regs X).toNat)).nextPc, zf, ?_, ?_⟩
  · show fstepF (loadN (regLay E.rs base) (liftReg D) A (liftReg X)) b zf = _
    rw [fstepF_loadN]
    simp only [lsemStepMem, loadN, loadStruct?, if_true, harr, h.getW hX, Option.map_some]
  · have hregs : ∀ r, (evalInstrA sa (.loadMemIdx D B X 8)).regs r
        = if r = D then stackGet arr (sa.regs X).toNat else sa.regs r := fun r => by
      show (if r = D then read64 sa.mem (sa.regs B
          + BitVec.ofInt 64 ((8 * (sa.regs X).toNat : Nat) : Int)) else sa.regs r) = _
      rw [addr_idx8 _ A _ _ hBv, hcell]
    refine h.write hD _ hregs rfl ?_ (fun hz => h.corr.zfEq hz) (fun _ ho => ho)
      (h.facts.write hregs)
    intro Y hY
    rcases live_kill (ws := [D]) (st := st) hY with hY | hY
    · exact Or.inl (List.mem_singleton.mp hY)
    · exact Or.inr hY

/-- **An indexed store through a register holding the base of a region.** -/
theorem decSim_lift_storeIdx (hsep : LSep E base rsp) {st : LiftSt} {B X V A : String}
    {δ : Nat} (hX : st.live X = true) (hV : st.live V = true) (hB : st.ptr.lookup B = some A)
    (hδ : st.bndOf X = some δ) (hle : E.nb + δ ≤ regLen E.rs A) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp st)
      [(.Lopn [.reg A] "STOREIDX" [.arrIdx A (liftReg X) 8, .reg (liftReg V)],
        .store 64 (regLen E.rs A))]
      [.storeMemIdx B X 8 (.reg V)] := by
  refine DecSim.single fun sa b zf h => ?_
  set j := (sa.regs X).toNat with hj
  have hK : regK E.rs A j := h.idx hδ hle
  obtain ⟨hjl, arr, harr, _⟩ := h.corr.cells A j hK
  have hBv : sa.regs B = (regLay E.rs base).base A := h.facts.ptr (B, A) (mem_of_lookup hB)
  refine ⟨(b.setArr A (stackSet arr j (sa.regs V))).nextPc, zf, ?_, ?_⟩
  · show fstepF (storeN (regLay E.rs base) A A (liftReg X) (liftReg V)) b zf = _
    rw [fstepF_storeN]
    simp only [lsemStepMem, storeN, storeStruct?, if_true, harr, h.getW hX, h.getW hV,
      Option.map_some]
    rfl
  · have hmem : (evalInstrA sa (.storeMemIdx B X 8 (.reg V))).mem
        = write64 sa.mem ((regLay E.rs base).addr A j) (sa.regs V) := by
      show write64 sa.mem (sa.regs B
        + BitVec.ofInt 64 ((8 * (sa.regs X).toNat : Nat) : Int)) (sa.regs V) = _
      rw [addr_idx8 _ A _ _ hBv]
    have hregs : (evalInstrA sa (.storeMemIdx B X 8 (.reg V))).regs = sa.regs := rfl
    have hfl : (evalInstrA sa (.storeMemIdx B X 8 (.reg V))).flags = sa.flags := rfl
    have hdisj : ∀ C k, regK E.rs C k → (regLay E.rs base).addr C k
        ≠ (regLay E.rs base).addr A j →
        Disjoint8 ((regLay E.rs base).addr A j) ((regLay E.rs base).addr C k) :=
      fun C k hCk hne => by
        rcases hsep.mem.sep.cells A j C k hjl (h.corr.cells C k hCk).1 with h' | h'
        · exact absurd h'.symm hne
        · exact h'
    refine
      { corr :=
          { regs := fun r hr => by
              rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc, hregs]
              exact h.corr.regs r hr
            zfEq := fun hz => by rw [hfl]; exact h.corr.zfEq hz
            cells := fun A' j' hk => ?_
            slots := fun C q hq => ?_ }
        sp := by rw [hregs]; exact h.sp
        sliveS := h.sliveS
        slots := fun off ho => ?_
        facts := h.facts.of_regs fun r => by rw [hregs] }
    · rw [hmem]
      by_cases hA : A' = A
      · subst hA
        by_cases hjj : j' = j
        · subst hjj
          refine ⟨hjl, stackSet arr j (sa.regs V), by simp, ?_⟩
          rw [read64_write64_same, stackGet_stackSet_same _ _ _ hjl]
        · obtain ⟨hj', arr', ha', hr'⟩ := h.corr.cells A' j' hk
          rw [harr] at ha'
          obtain rfl := Option.some.inj ha'
          have hne : (regLay E.rs base).addr A' j' ≠ (regLay E.rs base).addr A' j :=
            fun he => hjj (hsep.mem.inj A' j' A' j hk hK he).2
          refine ⟨hj', stackSet arr j (sa.regs V), by simp, ?_⟩
          rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne), hr',
            stackGet_stackSet_ne _ _ _ _ hjl hj' hjj]
      · obtain ⟨hj', arr', ha', hr'⟩ := h.corr.cells A' j' hk
        have hne : (regLay E.rs base).addr A' j' ≠ (regLay E.rs base).addr A j :=
          fun he => hA (hsep.mem.inj A' j' A j hk hK he).1
        rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne)]
        exact ⟨hj', arr', by simpa [hA] using ha', hr'⟩
    · rw [hmem]
      obtain ⟨aC, hqC, hpC⟩ := h.corr.slots C q hq
      refine ⟨aC, hqC, ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.mem.sep.slots A j C q aC hjl hq hqC)]
      exact hpC
    · rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc, hmem,
        read64_write64_of_disjoint _ _ _ _ (hsep.cell off (h.sliveS off ho) A j hK)]
      exact h.slots off ho

theorem live_kill_of {st : LiftSt} {ws : List String} {X : String} (h : st.live X = true) :
    (st.kill ws).live X = true := by
  have hX := mem_liftRegs_of_live h
  have hnd := not_dead_of_live h
  simp [LiftSt.live, LiftSt.kill, hX, hnd]

theorem Facts.holdsLo {st : LiftSt} {sa : AState} (h : Facts E base st sa) {D X Y : String}
    (hl : st.holdsLo D X Y = true) : sa.regs D = sa.regs X * sa.regs Y := by
  have key : ∀ a, (st.lo.contains (D, a, Y) = true ∨ st.lo.contains (D, Y, a) = true) →
      sa.regs D = sa.regs a * sa.regs Y := fun a ha => by
    simp only [List.contains_iff_mem] at ha
    rcases ha with ha | ha
    · exact h.lo _ ha
    · rw [h.lo _ ha]; exact BitVec.mul_comm _ _
  simp only [LiftSt.holdsLo, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hl
  rcases hl with hl | ⟨p, hp, rfl, hl⟩
  · exact key X hl
  · rw [key p.2 hl, h.cp p hp]

theorem evalInstrA_mulx_flags (sa : AState) (H Lo S C : String) :
    (evalInstrA sa (.mulx H Lo (.reg S) (.reg C))).flags = sa.flags := by
  simp [evalInstrA, evalInstr, AState.view, JState.setReg]

/-- **The high word of `mulx` whose low register already holds the low word.** -/
theorem decSim_lift_mulxHi {st : LiftSt} {H Lo C : String} (hH : H ∈ liftRegs) (hHL : H ≠ Lo)
    (hR : st.live "%rdx" = true) (hC : st.live C = true) (hl : st.holdsLo Lo "%rdx" C = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp (st.kill [H]))
      [opI "MULXHI" H [.reg (liftReg "%rdx"), .reg (liftReg C)]]
      [.mulx H Lo (.reg "%rdx") (.reg C)] := by
  refine DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_mulhiI _ _ _ b zf _ _ (h.getW hR) (h.getW hC), ?_⟩
  have hLo := h.facts.holdsLo hl
  have hregs : ∀ r, (evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C))).regs r
      = if r = H then mulHiW (sa.regs "%rdx") (sa.regs C) else sa.regs r := fun r => by
    rw [evalInstrA_mulx]
    by_cases h1 : r = H
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : r = Lo
      · subst h2; rw [if_pos rfl, hLo, RunBlockLsemAgree.mulLo_eq]
      · rw [if_neg h2]
  refine h.write hH _ hregs rfl ?_
    (fun hz => by rw [evalInstrA_mulx_flags]; exact h.corr.zfEq hz) (fun _ ho => ho)
    (h.facts.write hregs)
  intro X hX
  rcases live_kill (ws := [H]) (st := st) hX with hX | hX
  · exact Or.inl (List.mem_singleton.mp hX)
  · exact Or.inr hX

theorem live_kill_mem {st : LiftSt} {ws : List String} {X : String} (hX : X ∈ liftRegs)
    (hw : X ∈ ws) : (st.kill ws).live X = true := by
  simp [LiftSt.live, LiftSt.kill, hX, hw]

/-- The two words of `mulx` read back as `MULXHI` and `MUL`, in the order `first` (the high
    word first when `first = true`), when neither destination is a source of the instruction
    read second. -/
theorem decSim_lift_mulx2 {st : LiftSt} {H Lo C : String} (hH : H ∈ liftRegs)
    (hLo : Lo ∈ liftRegs) (hHL : H ≠ Lo) (hR : st.live "%rdx" = true) (hC : st.live C = true)
    (first : Bool) (hW : if first then H ≠ "%rdx" ∧ H ≠ C else Lo ≠ "%rdx" ∧ Lo ≠ C) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp (st.kill [H, Lo]))
      (if first then
        [opI "MULXHI" H [.reg (liftReg "%rdx"), .reg (liftReg C)],
          opI "MUL" Lo [.reg (liftReg "%rdx"), .reg (liftReg C)]]
      else
        [opI "MUL" Lo [.reg (liftReg "%rdx"), .reg (liftReg C)],
          opI "MULXHI" H [.reg (liftReg "%rdx"), .reg (liftReg C)]])
      [.mulx H Lo (.reg "%rdx") (.reg C)] := by
  intro sa b zf h
  set vd := sa.regs "%rdx"
  set vc := sa.regs C
  have hfin : ∀ r, (evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C))).regs r
      = if r = H then mulHiW vd vc else if r = Lo then vd * vc else sa.regs r := fun r => by
    rw [evalInstrA_mulx, RunBlockLsemAgree.mulLo_eq]; rfl
  have hfl := evalInstrA_mulx_flags sa H Lo "%rdx" C
  have hfacts : Facts E base (st.kill [H, Lo]) (evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C))) :=
    h.facts.kill [H, Lo] fun r hr => by
      rw [hfin, if_neg (fun e => hr (by simp [e])), if_neg (fun e => hr (by simp [e]))]
  have hlive2 : ∀ (W : String) (ws : List String), W ∈ [H, Lo] → ws = [W] →
      ∀ X, (st.kill [H, Lo]).live X = true → X = (if W = H then Lo else H) ∨
        (st.kill ws).live X = true := by
    intro W ws hWm hws X hX
    subst hws
    rcases live_kill (ws := [H, Lo]) (st := st) hX with hm | hX'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hWm
      rcases hWm with rfl | rfl <;> rcases hm with rfl | rfl <;> simp_all [live_kill_mem]
    · exact Or.inr (live_kill_of hX')
  cases first with
  | true =>
    simp only [if_true] at hW ⊢
    obtain ⟨hHR, hHC⟩ := hW
    let sa1 : AState := { sa with regs := fun r => if r = H then mulHiW vd vc else sa.regs r }
    have h1 : LCorr E base rsp (st.kill [H]) sa1
        ((b.setReg (liftReg H) (mulHiW vd vc)).nextPc) zf :=
      h.write hH _ (fun _ => rfl) rfl
        (fun X hX => by
          rcases live_kill (ws := [H]) (st := st) hX with hX | hX
          · exact Or.inl (List.mem_singleton.mp hX)
          · exact Or.inr hX)
        (fun hz => h.corr.zfEq hz) (fun _ ho => ho) (h.facts.write fun _ => rfl)
    have hR1 := h1.getW (live_kill_of (ws := [H]) hR)
    have hC1 := h1.getW (live_kill_of (ws := [H]) hC)
    have hR1v : sa1.regs "%rdx" = vd := if_neg (Ne.symm hHR)
    have hC1v : sa1.regs C = vc := if_neg (Ne.symm hHC)
    rw [hR1v] at hR1
    rw [hC1v] at hC1
    have hs2 := fstepF_binRegI (withWidthTag 64 "MUL") "MUL" (liftReg Lo) (liftReg "%rdx")
      (liftReg C) (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      _ zf vd hR1
    rw [hC1, Option.bind_some, show applyOpnN 64 "MUL" [vd, vc] = some (vd * vc) from rfl,
      Option.map_some] at hs2
    refine ⟨withALUFlags (binRegI (withWidthTag 64 "MUL") (liftReg Lo) (liftReg "%rdx")
      (liftReg C)) ((b.setReg (liftReg H) (mulHiW vd vc)).nextPc)
      (((b.setReg (liftReg H) (mulHiW vd vc)).nextPc.setReg (liftReg Lo) (vd * vc)).nextPc),
      zf, ?_, ?_⟩
    · show runStraightF [mulhiI (liftReg H) (liftReg "%rdx") (liftReg C),
        binRegI (withWidthTag 64 "MUL") (liftReg Lo) (liftReg "%rdx") (liftReg C)] b zf = _
      rw [runStraightF_cons, fstepF_mulhiI _ _ _ b zf _ _ (h.getW hR) (h.getW hC),
        Option.bind_some, runStraightF_cons, hs2]
      rfl
    · show LCorr E base rsp (st.kill [H, Lo]) (evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C)))
        _ zf
      refine LCorr.withALUFlags (h1.write (st' := st.kill [H, Lo])
        (sa' := evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C))) hLo (vd * vc)
        (fun r => ?_) rfl (fun X hX => by simpa using hlive2 H [H] (by simp) rfl X hX)
        (fun hz => by rw [hfl]; exact h.corr.zfEq hz) (fun _ ho => ho) hfacts) _ _
      rw [hfin]
      by_cases h1 : r = H
      · subst h1; simp [hHL, sa1]
      · simp [h1, sa1]
  | false =>
    simp only [Bool.false_eq_true, if_false] at hW ⊢
    obtain ⟨hLR, hLC⟩ := hW
    let sa1 : AState := { sa with regs := fun r => if r = Lo then vd * vc else sa.regs r }
    have hs1 := fstepF_binRegI (withWidthTag 64 "MUL") "MUL" (liftReg Lo) (liftReg "%rdx")
      (liftReg C) (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
      b zf vd (h.getW hR)
    rw [h.getW hC, Option.bind_some, show applyOpnN 64 "MUL" [vd, vc] = some (vd * vc) from rfl,
      Option.map_some] at hs1
    let b1 := withALUFlags (binRegI (withWidthTag 64 "MUL") (liftReg Lo) (liftReg "%rdx")
      (liftReg C)) b ((b.setReg (liftReg Lo) (vd * vc)).nextPc)
    have h1 : LCorr E base rsp (st.kill [Lo]) sa1 b1 zf :=
      LCorr.withALUFlags (h.write (st' := st.kill [Lo]) (sa' := sa1) hLo _ (fun _ => rfl) rfl
        (fun X hX => by
          rcases live_kill (ws := [Lo]) (st := st) hX with hX | hX
          · exact Or.inl (List.mem_singleton.mp hX)
          · exact Or.inr hX)
        (fun hz => h.corr.zfEq hz) (fun _ ho => ho) (h.facts.write fun _ => rfl)) _ _
    have hR1 := h1.getW (live_kill_of (ws := [Lo]) hR)
    have hC1 := h1.getW (live_kill_of (ws := [Lo]) hC)
    have hR1v : sa1.regs "%rdx" = vd := if_neg (Ne.symm hLR)
    have hC1v : sa1.regs C = vc := if_neg (Ne.symm hLC)
    rw [hR1v] at hR1
    rw [hC1v] at hC1
    refine ⟨(b1.setReg (liftReg H) (mulHiW vd vc)).nextPc, zf, ?_, ?_⟩
    · show runStraightF [binRegI (withWidthTag 64 "MUL") (liftReg Lo) (liftReg "%rdx")
        (liftReg C), mulhiI (liftReg H) (liftReg "%rdx") (liftReg C)] b zf = _
      rw [runStraightF_cons, hs1, Option.bind_some, runStraightF_cons,
        fstepF_mulhiI _ _ _ b1 zf _ _ hR1 hC1]
      rfl
    · show LCorr E base rsp (st.kill [H, Lo]) (evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C)))
        _ zf
      refine h1.write (st' := st.kill [H, Lo])
        (sa' := evalInstrA sa (.mulx H Lo (.reg "%rdx") (.reg C))) hH (mulHiW vd vc)
        (fun r => ?_) rfl (fun X hX => by
          simpa [Ne.symm hHL] using hlive2 Lo [Lo] (by simp) rfl X hX)
        (fun hz => by rw [hfl]; exact h.corr.zfEq hz) (fun _ ho => ho) hfacts
      rw [hfin]

/-- **A compare of two registers.** -/
theorem decSim_lift_cmpReg {st : LiftSt} {A X : String} (hA : st.live A = true)
    (hX : st.live X = true) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st with zl := true })
      [cmpRI (liftReg A) (.reg (liftReg X))] [.cmp A (.reg X)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, _, fstepF_cmpRI _ _ b zf _ _ (h.getW hA) (h.getW hX),
      h.cmp (evalInstrA_cmp_regs sa A _) rfl (evalInstrA_cmp_reg_zf sa A X)⟩

/-- **A compare with an immediate.** -/
theorem decSim_lift_cmpImm {st : LiftSt} {A : String} (hA : st.live A = true) (k : Nat) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp { st with zl := true })
      [cmpRI (liftReg A) (.imm k)] [.cmp A (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, _, fstepF_cmpRI _ _ b zf _ _ (h.getW hA) rfl,
      h.cmp (evalInstrA_cmp_regs sa A _) rfl (by
        show (some (ZF_of_word (sa.regs A - BitVec.ofNat 64 k))).getD false = _
        rw [ZF_of_word_sub]; rfl)⟩

/-! ## 7. The reading -/

/-- **An instruction read back is simulated by its machine instruction.** -/
theorem liftInstr_sound (hsep : LSep E base rsp) {st st' : LiftSt} {j : JInstr 64}
    {ls : List LinstrRM} (h : liftInstr E st j = some (st', ls)) :
    DecSim (LCorr E base rsp st) (LCorr E base rsp st') ls [j] := by
  have hpair : ∀ {a a' : LiftSt} {l l' : List LinstrRM}, some (a, l) = some (a', l') →
      a = a' ∧ l = l' := fun h => by simpa using h
  unfold liftInstr at h
  split at h
  · rename_i S B off
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, List.contains_iff_mem] at hc
    obtain ⟨rfl, hS⟩ := hc
    split at h
    · rename_i g hg
      split at h
      · cases h
      rename_i hgr
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hgr
      obtain ⟨rfl, rfl⟩ := hpair h
      have hoff : g.off = off := by simpa using List.find?_some hg
      subst hoff
      exact decSim_lift_reload hS hgr
    · split at h
      · rename_i ho
        obtain ⟨rfl, rfl⟩ := hpair h
        exact decSim_lift_slotLoad hS (List.contains_iff_mem.mp ho)
      · cases h
  · rename_i B off X
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨rfl, hX⟩, hoS⟩, -⟩ := hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_slotStore hsep hX hoS
  · rename_i D B X sc
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨hD, -⟩, hX⟩, rfl⟩ := hc
    split at h
    · rename_i A δ hB hδ
      split at h
      · rename_i hle
        obtain ⟨rfl, rfl⟩ := hpair h
        exact decSim_lift_loadIdx hD hX hB hδ hle
      · cases h
    · cases h
  · rename_i B X sc V
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨-, hX⟩, hV⟩, rfl⟩ := hc
    split at h
    · rename_i A δ hB hδ
      split at h
      · rename_i hle
        obtain ⟨rfl, rfl⟩ := hpair h
        exact decSim_lift_storeIdx hsep hX hV hB hδ hle
      · cases h
    · cases h
  · rename_i D X
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
      List.contains_iff_mem] at hc
    obtain ⟨hD, -⟩ := hc
    split at h
    · obtain ⟨rfl, rfl⟩ := hpair h
      exact decSim_lift_movDead hD
    · rename_i hX
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hX
      obtain ⟨rfl, rfl⟩ := hpair h
      split
      · rename_i hXD
        obtain rfl := beq_iff_eq.mp hXD
        exact decSim_lift_movSelf hX
      · rename_i hXD
        exact decSim_lift_movReg hD hX (fun e => hXD (beq_iff_eq.mpr e))
  · rename_i D n
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
      List.contains_iff_mem] at hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_movImm hc.1 n
  · rename_i D k
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    obtain ⟨rfl, rfl⟩ := hpair h
    have he : opI "ADD" D [.reg (liftReg D), .imm k] = addImmI (liftReg D) (liftReg D) k := by
      simp [opI, addImmI, withWidthTag]
    rw [he]
    exact decSim_lift_addImm hc k
  · rename_i D k
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    obtain ⟨rfl, rfl⟩ := hpair h
    have he : opI "SUB" D [.reg (liftReg D), .imm k] = subImmI (liftReg D) (liftReg D) k := by
      simp [opI, subImmI, withWidthTag]
    rw [he]
    exact decSim_lift_subImm hc k
  · rename_i D k
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, beq_iff_eq,
      decide_eq_false_iff_not, Decidable.not_not] at hc
    obtain ⟨⟨hD, hk0⟩, hk⟩ := hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_shr hD hk0 hk
  · rename_i D k
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, beq_iff_eq,
      decide_eq_false_iff_not, Decidable.not_not] at hc
    obtain ⟨⟨hD, hk0⟩, hk⟩ := hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_shl hD hk0 hk
  · rename_i H Lo S C
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, beq_iff_eq, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨rfl, hHL⟩, hH⟩, hLo⟩, hR⟩, hC⟩ := hc
    split at h
    · rename_i hl
      obtain ⟨rfl, rfl⟩ := hpair h
      exact decSim_lift_mulxHi hH hHL hR hC hl
    · split at h
      · rename_i hw
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
        obtain ⟨rfl, rfl⟩ := hpair h
        exact decSim_lift_mulx2 hH hLo hHL hR hC true hw
      · split at h
        · rename_i hw
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
          obtain ⟨rfl, rfl⟩ := hpair h
          exact decSim_lift_mulx2 hH hLo hHL hR hC false hw
        · cases h
  · rename_i A X
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_cmpReg hc.1 hc.2
  · rename_i A k
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_cmpImm hc k
  · rename_i A B off
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
      Decidable.not_not, Bool.not_eq_false, List.contains_iff_mem] at hc
    obtain ⟨⟨rfl, hA⟩, ho⟩ := hc
    obtain ⟨rfl, rfl⟩ := hpair h
    exact decSim_lift_cmpMem hA ho
  · dsimp only at h
    split at h
    · rename_i opn Y st'' hb
      unfold binRegLift at hb
      have fin : ∀ {D Y' : String} {opn' : String} {st₀ : LiftSt},
          (if (!st.live D || !st.live Y') = true then none
            else some (st₀, [opI opn' D [LOperand.reg (liftReg D), LOperand.reg (liftReg Y')]]))
            = some (st', ls) →
          st.live D = true ∧ st.live Y' = true ∧ st' = st₀ ∧
            ls = [opI opn' D [LOperand.reg (liftReg D), LOperand.reg (liftReg Y')]] := by
        intro D Y' opn' st₀ h
        split at h
        · cases h
        · rename_i hc
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
          obtain ⟨rfl, rfl⟩ := hpair h
          exact ⟨hc.1, hc.2, rfl, rfl⟩
      split at hb <;> (try dsimp only at hb) <;>
        simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_add hD hY
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_sub hD hY
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_and hD hY
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_xor hD hY
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_or hD hY
      · obtain ⟨rfl, rfl, rfl⟩ := hb
        obtain ⟨hD, hY, rfl, rfl⟩ := fin h
        exact decSim_lift_imul hD hY
    · cases h

/-- **A body read back is simulated by its machine instructions.** -/
theorem liftRun_sound (hsep : LSep E base rsp) :
    ∀ {st st' : LiftSt} {js : List (JInstr 64)} {ls : List LinstrRM},
      liftRun E st js = some (st', ls) →
      DecSim (LCorr E base rsp st) (LCorr E base rsp st') ls js
  | st, st', [], ls, h => by
      simp only [liftRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact DecSim.nil _
  | st, st', j :: js, ls, h => by
      simp only [liftRun] at h
      obtain ⟨⟨st1, is⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨st2, is'⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
      simp only [Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      exact (liftInstr_sound hsep h1).append (liftRun_sound hsep h3)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLoopTVSound
