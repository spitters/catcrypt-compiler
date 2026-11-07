/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

@[expose] public section

set_option autoImplicit false

/-!
# The address-machine correspondence with one-bit carry registers

`DecodePrintedAddr.ACorr` relates every general-purpose name of the address machine to its
machine register at width `64`. The carry chain of the address machine keeps a carry in a
name at width `1` (`ADCXHI` writes `carryOutBit`, `ADCX` reads its carry-in at width `1`),
while the machine keeps it in a 64-bit register as `0` or `1`. `ACorrW` relates such a name
to the zero-extension of its bit. A width cast leaves a name at width `32` or `16`
(`NarrowCell`): a 32-bit value is related to the register that zero-extends it, as an x86
32-bit write leaves it, and a 16-bit value to a register whose low 16 bits hold it, as an x86
16-bit write keeps the upper 48 bits.

An arm of `DecodePrintedAddr` reads every general-purpose name at width `64` (`WideAt`). Its
step from a state related by `ACorrW` is the step from the state with every general-purpose
name at a narrow width replaced by its machine register (`widenS`), which `ACorr` relates, up to the congruence `JasminLsemAddrCongr.fstepA_congr`
in the names the instruction reads (`AArm.simW`). The frame-word store of a one-bit name
(`bitSrc`) stores the zero-extension of the bit, which the machine register holds
(`AArm.simW_st1`), and a copy of a one-bit name between general-purpose names, also of
`bitSrc`, gives its destination the bit, whose zero-extension the machine register of the
destination holds after the copy (`AArm.simW_copy1`).

The carry arms (`CArm`) are the add `ADCX:64 D, A, S, C`, printed `bt $0, C; adcx S, D` after
the copy of `A` into `D`, and its carry-out binding `ADCXHI:64 O, A, S, C`, printed `setc O`;
the binding reads the carry flag the add leaves, which the run threads to it (`CarryAt`). The
cell arms (`MArm`) are the whole-word load and store of a cell `mem.B.off` and the 64-bit moves
`MOV:64 mem.B.off, S` into and `MOV:64 D, mem.B.off` out of a cell, printed `mov off(%B)`.
The carry constant, an untagged `MOV D, #n` with `n < 2` that the address
machine steps at the one-bit tag (`JasminLsemAddrRun.tagAt`), is printed `mov $n, %r32`, which
leaves the zero-extension of the bit in the register. The wide immediate, `MOV:64 D, #v` with
`v` outside the sign-extended `imm32` range, is printed `movabs $v, %r64`; into a frame slot it
is printed through `%rax`, saved to and restored from the red-zone word. The register select
`CMOV:64 D, [C, A, B]` reads its condition `C` at width `1`, like a carry-in (`carryIns`), and
is printed `test C, C` followed by a conditional move; a false value in a frame slot is loaded
into `D` before the test, and a true value in a frame slot is read by `cmovne` from its frame
word. The class `printedAddrWB` adds these
arms to the bodies of `DecodePrintedCFG`.

## Main definitions

* `NarrowCell` — the 32- and 16-bit cells of a machine register.
* `widenS` — the address state with each general-purpose name at width `1`, `16` or `32`
  replaced by its machine register at width `64`.
* `ACorrW` — the correspondence with one-bit, 16-bit and 32-bit names.
* `WideAt` — every general-purpose name an instruction reads is at width `64`.
* `CArm`, `MArm` — the carry and cell arms.
* `printedAddrWB`, `SafeW` — the covered bodies and the run safety they are simulated under.
* `classifyK`, `narrowIn`, `NarrowInv`, `castPosB` — the cast arm, the widths the run of
  consecutive casts before a position gives its destinations, and the check that a cast
  keeps the low bits its source and destination widths give.

## Main results

* `ACorr.toW`, `ACorrW.widen`: `ACorr` is the case of `ACorrW` without narrow names, and an
  `ACorrW` state widens to an `ACorr` state.
* `fstepA_castW`, `sim_castW`: a width cast at the descriptor tag is the typed cast step
  `lsemStepCast`, and `movzx` of the low 8, 16 or 32 bits simulates it into a 64-, 32- or
  16-bit cell.
* `castBytes`, `sim_castW_bytes`: the bytes of a width-carrying cast `CASTW_<w>_<w'>` are
  one piece that decodes to `movzx`, and its decoded instruction simulates the cast step.
* `AArm.simW`: an arm of `DecodePrintedAddr` steps from `ACorrW` to `ACorrW`.
* `AArm.simW_of`, `AArm.simW_st1`: the same from steps on the state and on the widened state
  that agree up to `AStep`, and the frame-word store of a one-bit name.
* `SArm.bytes`, `sim_sadcx`, `sim_sadcxhi`, `sim_sadcxc`: the bytes and the simulations of the
  carry arms with frame-slot operands; an add whose carry-in is a frame slot is printed as the
  save of a scratch in the red-zone word, the reload of the carry-in word, `bt $0` of the
  scratch (`run_cPre`) and the add in the scratch or, after the restore, in the register
  destination.
* `CArm.bytes`, `sim_adcx`, `sim_adcxhi`, `MArm.bytes`, `sim_ldm`, `sim_stm`, `sim_stv`,
  `sim_ldv`, `zBytes`,
  `sim_bmov`, `lBytes`, `sim_lmov`, `vBytes`, `sim_cmov`: the bytes and the simulations of
  the carry, cell, carry-constant, wide-immediate and register-select arms.
* `imm32Ok`, `imm32Bytes`, `fstepA_immMov32`, `sim_imov`: an untagged immediate move that is
  no carry constant is a 32-bit constant, held in a 32-bit cell (`NarrowCell`).
* `vtBytes`, `sim_cmovSlot`, `vfBytes`, `sim_cmovSlotF`, `veBytes`, `sim_cmovSlotFE`: the bytes
  and the simulations of the selects with a slot true value and with a slot false value, the
  latter with the destination other than or equal to the true value.
* `eBytes`, `fstepA_sete`, `runBlock_ePieces`, `sim_sete`, `instrOKWB_sete`: the materialised
  comparison `SETE:64`/`SETNE:64 D, [A, B]` on general-purpose names is printed as `cmp`,
  `mov $0` and `set<cc>`, whose run writes the zero-extended comparison bit the address step
  writes at width `1`; `instrOKWB` accepts every such instruction.
* `xBytes`, `fstepA_shrx`, `runBlock_xPieces`, `sim_shrx`, `instrOKWB_shrReg`: the
  register-count shift `SHL:64`/`SHR:64 D, [A, B]` on general-purpose names is printed as the
  BMI2 `shlx`/`shrx`, whose count mask is the mask of the address step; `instrOKWB` accepts
  every such instruction.
* `eiBytes`, `fstepA_seteImm`, `runBlock_eiPieces`, `sim_seteImm`, `instrOKWB_seteImm`: the
  materialised comparison `SETE:64`/`SETNE:64 D, [A, $v]` with an immediate `v < 2^31` is
  printed as `cmp $v`, `mov $0` and `set<cc>`; `instrOKWB` accepts every such instruction.
* `rBytes_encode`, `fstepA_sarImm`, `runBlock_rPieces`, `sim_sarImm`, `instrOKWB_sarImm`: the
  arithmetic right shift `SAR:64 D, [D, #k]` of a general-purpose name in place by
  `0 < k < 64` is printed as `sar $k`, whose run writes the arithmetic shift the address step
  writes; `instrOKWB` accepts every such instruction.
* `narrowInv_step`, `runSafe_narrow`: every step of the address machine keeps `NarrowInv`.
* `BodyFactsCW`, `step_simWN`: one step of the address machine at a covered instruction is
  matched by a path on any program holding the decoded instructions of the position
  (`blkOf`), in a body that may hold remote transfers.
* `run_simWN`, `run_simW`, `printedAddr_simW_noCall`, `printedAddr_simW`: the decoded bytes
  of a body in `printedAddrWB` simulate its run on the address machine, by a halting run
  without a call; the induction iterates `step_simWN`.
* `printedAddrWB_eq_impl` (`@[csimp]`): the gate is evaluated with the body parameters
  computed once per body, the carry-out and cast gates on the array of the body
  (`carryPrevBA`, `castPosBA`) and the cast width analyses tabulated (`narrowTable`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

/-! ## 1. The correspondence -/

/-- The widths of the narrow cells of a general-purpose name: `1`, `16` and `32`. -/
def narrowW (w : Nat) : Bool := w == 1 || w == 16 || w == 32

/-- **The 16- and 32-bit cells.** The cell `c` of a general-purpose name whose machine register
    holds `v` is a 32-bit value whose zero-extension `v` is (an x86 32-bit write zero-extends
    into the 64-bit register), or a 16-bit value that the low 16 bits of `v` hold (an x86
    16-bit write keeps the upper 48 bits). -/
def NarrowCell (c : Σ w, BitVec w) (v : BitVec 64) : Prop :=
  (∃ b : BitVec 32, c = ⟨32, b⟩ ∧ v = b.setWidth 64)
    ∨ (∃ b : BitVec 16, c = ⟨16, b⟩ ∧ v.setWidth 16 = b)

theorem NarrowCell.width {c : Σ w, BitVec w} {v : BitVec 64} (h : NarrowCell c v) :
    c.1 = 32 ∨ c.1 = 16 := by
  rcases h with ⟨b, rfl, -⟩ | ⟨b, rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The cell of name `r` widened against the machine register value `v`: a cell of a
    general-purpose name at a narrow width (`narrowW`) replaced by `v` at width `64`, any other
    cell unchanged. -/
def widenCell (r : String) (v : BitVec 64) (c : Σ w, BitVec w) : Σ w, BitVec w :=
  if (gpOk r && narrowW c.1) = true then ⟨64, v⟩ else c

/-- The address state with every general-purpose name at a narrow width replaced by its
    machine register in `sa` at width `64`. -/
def widenS (sa : AState) (s : LstateA) : LstateA :=
  { s with reg := { s.reg with lvm := fun r => widenCell r (sa.regs (phys r)) (s.reg.lvm r) } }

/-- **The correspondence with narrow names.** Each general-purpose name holds the value of
    its machine register at width `64`, a bit whose zero-extension the machine register
    holds, or a 32- or 16-bit cell (`NarrowCell`); the stack register holds `rsp`; the
    memories agree outside the red-zone word. -/
structure ACorrW (rsp : BitVec 64) (sa : AState) (s : LstateA) : Prop where
  /-- A general-purpose name holds its machine register, a bit it zero-extends, or a 32- or
      16-bit cell of it. -/
  regs : ∀ r, gpOk r = true → s.reg.getW r 64 = some (sa.regs (phys r))
    ∨ (∃ b : BitVec 1, s.reg.lvm r = ⟨1, b⟩ ∧ sa.regs (phys r) = b.setWidth 64)
    ∨ NarrowCell (s.reg.lvm r) (sa.regs (phys r))
  /-- The stack register holds `rsp`. -/
  sp : sa.regs "%rsp" = rsp
  /-- The memories agree outside the red-zone word. -/
  mem : ∀ x, ¬ InRange8 (redW rsp) x → s.mem x = sa.mem x

theorem ACorr.toW {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorr rsp sa s) :
    ACorrW rsp sa s :=
  ⟨fun r hr => Or.inl (h.regs r hr), h.sp, h.mem⟩

theorem lvm_of_getW {s : LstateN} {r : String} {v : BitVec 64} (h : s.getW r 64 = some v) :
    s.lvm r = ⟨64, v⟩ :=
  getW_eq_some_iff.1 h

/-- A cell related to its machine register by `ACorrW` at a narrow width widens to that
    register. -/
theorem widenCell_of_regs {r : String} (hr : gpOk r = true) {v : BitVec 64}
    {c : Σ w, BitVec w} (h : (c = ⟨64, v⟩) ∨ (∃ b : BitVec 1, c = ⟨1, b⟩ ∧ v = b.setWidth 64)
      ∨ NarrowCell c v) :
    widenCell r v c = ⟨64, v⟩ := by
  rcases h with rfl | ⟨b, rfl, -⟩ | ⟨b, rfl, -⟩ | ⟨b, rfl, -⟩ <;> simp [widenCell, narrowW, hr]

theorem ACorrW.widen {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s) :
    ACorr rsp sa (widenS sa s) where
  regs r hr := by
    rw [getW_eq_some_iff]
    show widenCell r (sa.regs (phys r)) (s.reg.lvm r) = _
    apply widenCell_of_regs hr
    rcases h.regs r hr with hg | hb | hn
    · exact Or.inl (lvm_of_getW hg)
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hn)
  sp := h.sp
  mem := h.mem

/-- Every general-purpose name the instruction reads holds a 64-bit value. -/
def WideAt (s : LstateA) (i : LinstrR) : Prop :=
  ∀ r, readsI i r → gpOk r = true → (s.reg.lvm r).1 = 64

theorem aagree_widen {sa : AState} {s : LstateA} {i : LinstrR} (hw : WideAt s i) :
    AAgree (readsI i) s (widenS sa s) := by
  refine ⟨⟨rfl, fun r hr => ?_⟩, rfl, rfl, rfl⟩
  show s.reg.lvm r = widenCell r (sa.regs (phys r)) (s.reg.lvm r)
  by_cases hg : gpOk r = true
  · have h1 := hw r hr hg
    simp [widenCell, narrowW, h1]
  · simp [widenCell, hg]

/-! ## 2. The arms of `DecodePrintedAddr` -/

/-- A read name keeps its 64-bit value under widening. -/
theorem getW_widen {sa : AState} {s : LstateA} {i : LinstrR} (hw : WideAt s i) {r : String}
    (hr : readsI i r) (w : Nat) : (widenS sa s).reg.getW r w = s.reg.getW r w :=
  ((getW_congr (aagree_widen hw).1 hr w)).symm

/-- **An arm of `DecodePrintedAddr` on the correspondence with narrow names, from a step on
    the widened state.** From `ACorrW`, an arm whose indexed load is safe on the widened state
    `widenS` and whose address step from the state and from the widened state agree up to
    `AStep` steps, if the address machine steps, to a state that `ACorrW` relates to the
    machine run of the arm's decoded instructions; after a compare the machine zero flag is
    the flag of the address machine. -/
theorem AArm.simW_of (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hsafe' : a.LoadSafe rsp (widenS sa s)) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) a.li s zf = some (s', zf'))
    (hcg : ORel (AStep s (widenS sa s)) (fstepA (frameP P rsp) a.li s zf)
      (fstepA (frameP P rsp) a.li (widenS sa s) zf)) :
    ACorrW rsp (aMachine.runBlock sa (a.js P)) s'
      ∧ (cmpArmB a = true → (aMachine.runBlock sa (a.js P)).flags.zf.getD false = zf') := by
  obtain ⟨t', zt, h1, h2, h3⟩ := AArm.sim P rsp a h sa (widenS sa s) zf hc.widen hsafe'
  rw [hst, h1] at hcg
  cases hcg with
  | some hs =>
    obtain ⟨hn, hmem, -, -, hz⟩ := hs
    simp only at hn hmem hz
    subst hz
    refine ⟨⟨fun r hr => ?_, h2.sp, fun x hx => by rw [hmem]; exact h2.mem x hx⟩, h3⟩
    rcases hn.2 r with he | ⟨he1, he2⟩
    · left
      unfold LstateN.getW
      rw [he]
      exact h2.regs r hr
    · have hreg := h2.regs r hr
      rw [getW_eq_some_iff] at hreg
      rw [he2] at hreg
      change widenCell r (sa.regs (phys r)) (s.reg.lvm r) = _ at hreg
      have hg' : s'.reg.getW r 64 = s.reg.getW r 64 := by unfold LstateN.getW; rw [he1]
      by_cases hnw : narrowW (s.reg.lvm r).1 = true
      · simp only [widenCell, hr, hnw, Bool.and_self, ite_true, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at hreg
        rw [hg', he1, ← hreg]
        exact hc.regs r hr
      · left
        rw [getW_eq_some_iff, he1]
        simpa [widenCell, hnw] using hreg

/-- **An arm of `DecodePrintedAddr` on the correspondence with narrow names.** From
    `ACorrW`, an arm that reads its names at width `64` and whose indexed load is safe steps, if the
    address machine steps, to a state that `ACorrW` relates to the machine run of the arm's
    decoded instructions; after a compare the machine zero flag is the flag of the address
    machine. -/
theorem AArm.simW (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hw : WideAt s a.li.fst)
    (hsafe : a.LoadSafe rsp s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) a.li s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (a.js P)) s'
      ∧ (cmpArmB a = true → (aMachine.runBlock sa (a.js P)).flags.zf.getD false = zf') := by
  have hsafe' : a.LoadSafe rsp (widenS sa s) := by
    cases a with
    | ldx D B I =>
      intro p vi hp hvi
      have hB : readsI (AArm.ldx D B I).li.fst B := by
        show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) B
        exact base_reads (List.mem_singleton_self _)
      have hI : readsI (AArm.ldx D B I).li.fst I := by
        show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) I
        exact idx_reads (List.mem_singleton_self _)
      rw [getW_widen hw hB] at hp
      rw [getW_widen hw hI] at hvi
      exact hsafe p vi hp hvi
    | _ => trivial
  exact AArm.simW_of P rsp a h sa s zf hc hsafe' s' zf' hst
    (fstepA_congr (frameP P rsp) a.li (aagree_widen (sa := sa) hw) zf)

/-- **The frame-word store of a one-bit name on the correspondence with narrow names.** The
    store arm `m q, S` with `S` holding a bit steps, if the address machine steps, to a state
    that `ACorrW` relates to the machine run of the arm: the machine register of `S` holds the
    zero-extension of the bit, which the address machine stores. -/
theorem AArm.simW_st1 (P : Params) (rsp : BitVec 64) (m q S : String)
    (h : (AArm.st m q S).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) {b : BitVec 1} (hb : s.reg.lvm S = ⟨1, b⟩) (s' : LstateA)
    (zf' : Bool) (hst : fstepA (frameP P rsp) (AArm.st m q S).li s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((AArm.st m q S).js P)) s' := by
  have hok := h
  simp only [AArm.ok, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hS, -⟩, hsome⟩, -⟩, hm⟩ := hok
  have hm' : m = "MOVQ" ∨ m = "MOV:64" := by
    simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm; exact hm.symm
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
  have hfq : frameP P rsp q = some (rsp + BitVec.ofInt 64 off) := by simp [frameP, hoff]
  have hmv : slotMov? (AArm.st m q S).li.fst = some (q, S) := by
    rcases hm' with rfl | rfl <;>
      simp (config := { decide := true }) [AArm.li, AArm.instr, slotMov?,
        cellParts?_of_spillOff hsome, cellParts?_gp hS]
  have htag : (AArm.st m q S).li = ((AArm.st m q S).li.fst, .reg none) := by
    rcases hm' with rfl | rfl <;> rfl
  have hphys : sa.regs (phys S) = b.setWidth 64 := by
    rcases hc.regs S hS with h1 | ⟨b', h1, h2⟩ | h1
    · rw [getW_eq_some_iff, hb] at h1; cases h1
    · rw [hb] at h1
      obtain ⟨-, h1⟩ := Sigma.mk.inj_iff.mp h1
      rw [h2, eq_of_heq h1]
    · have := h1.width; rw [hb] at this; simp at this
  have hwS : (widenS sa s).reg.lvm S = ⟨64, b.setWidth 64⟩ := by
    show widenCell S (sa.regs (phys S)) (s.reg.lvm S) = _
    simp [widenCell, hb, hS, narrowW, hphys]
  have hs1 : fstepA (frameP P rsp) ((AArm.st m q S).li.fst, .reg none) s zf
      = some (⟨s.reg.nextPc, write64 s.mem (rsp + BitVec.ofInt 64 off) (b.setWidth 64), s.cf,
          s.of⟩, zf) :=
    fstepA_slotStore1 (frameP P rsp) hmv (frameP_gp hS) hfq s zf hb
  have ht1 : fstepA (frameP P rsp) ((AArm.st m q S).li.fst, .reg none) (widenS sa s) zf
      = some (⟨(widenS sa s).reg.nextPc, write64 s.mem (rsp + BitVec.ofInt 64 off)
          (b.setWidth 64), s.cf, s.of⟩, zf) := by
    have hgw : (widenS sa s).reg.getW S 64 = some (b.setWidth 64) := getW_eq_some_iff.mpr hwS
    simp only [fstepA, hmv, hfq, frameP_gp hS, hgw]
    rfl
  rw [htag] at hst
  refine (AArm.simW_of P rsp (AArm.st m q S) h sa s zf hc trivial s' zf' (by rw [htag]; exact hst)
    ?_).1
  rw [htag, hs1, ht1]
  exact .some ⟨⟨rfl, fun _ => Or.inr ⟨rfl, rfl⟩⟩, rfl, rfl, rfl, rfl⟩

/-! ## 3. The bytes of the carry chain -/

/-- `ADCX:64 D, A, S, C` between general-purpose names: the copy of `A` into `D` unless they
    coincide, `bt $0, C`, and `adcx S, D`. -/
theorem encodeLopn_adcx3 (F W : Nat) (D A S C : String) (qB : Nat) (hD : gpOk D = true)
    (hA : gpOk A = true) (hS : gpOk S = true) (hC : gpOk C = true) :
    encodeLopn F W (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]) qB
      = (if A = D then [] else encAluRRw 1 0x89 (gpNumU D) (gpNumU A))
        ++ encBtImm 1 (gpNumU C) 0 ++ ScalarEncoder.encAdxCarry 0x66 (gpNumU D) (gpNumU S) := by
  have fD := gpFacts hD
  have fA := gpFacts hA
  have fS := gpFacts hS
  have fC := gpFacts hC
  have hst : stripWidthTag "ADCX:64" = "ADCX" := by decide +kernel
  have hpx : adxPrefix "ADCX" = some 0x66 := rfl
  by_cases hAD : A = D
  · subst hAD
    simp (config := { decide := true }) [encodeLopn, fA.notSlot, fA.notMem, fS.notSlot,
      fS.notMem, fC.notSlot, fC.notMem, LprogBytes.rexW, hst, hpx]
  · simp (config := { decide := true }) [encodeLopn, fD.notSlot, fD.notMem, fA.notSlot,
      fA.notMem, fS.notSlot, fS.notMem, fC.notSlot, fC.notMem, hAD, LprogBytes.rexW, hst, hpx]

/-- `ADCXHI:64 O, A, S, C`: the carry flag materialised into `O` by `setc` and `movzbq`. -/
theorem encodeLopn_adcxhi3 (F W : Nat) (O A S C : String) (qB : Nat) (hO : gpOk O = true) :
    encodeLopn F W (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]) qB
      = encSetccMovzx 0x92 (gpNumU O) :=
  LprogBytes.encodeLopn_adcxhi F W O [.reg A, .reg S, .reg C] (gpFacts hO).isGp

open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

/-- `bt $0, %c`. -/
theorem pieceDec_bt (c : Nat) (hc : c < 16) :
    PieceDec (encBtImm 1 c 0, .bt (SailX86Decoder.regName c) (.imm 0)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_bt (canonAlloc ()) (SailX86Decoder.regName c) 0 rest (by decide)
  have he : encBtImm 1 c 0 = ScalarEncoder.encBtImm8 c 0 := by
    simp [encBtImm, ScalarEncoder.encBtImm8, rexOpt_w1]
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon hc,
    gpNum_regName hc, he] using e

/-- `adcx %s, %d`. -/
theorem pieceDec_adcx (d s : Nat) (hd : d < 16) (hs : s < 16) :
    PieceDec (ScalarEncoder.encAdxCarry 0x66 d s,
      .adcx (SailX86Decoder.regName d) (.reg (SailX86Decoder.regName s))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_adcx (canonAlloc ()) (SailX86Decoder.regName d) (SailX86Decoder.regName s)
    rest
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon hd,
    regOf_canon hs, gpNum_regName hd, gpNum_regName hs] using e

/-- `setc %o` and `movzbq`. -/
theorem pieceDec_setc (o : Nat) (ho : o < 16) :
    PieceDec (encSetccMovzx 0x92 o, .setc (SailX86Decoder.regName o)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have he : encSetccMovzx 0x92 o = ScalarEncoder.encSetcMovzx o := by
    interval_cases o <;> rfl
  rw [he]
  exact decodeJ1_encSetcMovzx o ho rest

/-! ## 4. The address-machine steps of the carry chain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry

/-- The address machine steps `ADCX:64 D, A, S, C` on registers by writing `addCarryWord` of
    the 64-bit values of `A`, `S` and the bit of `C` (`regBit`) to `D`. -/
theorem fstepA_adcx3 (frame : String → Option (BitVec 64)) (D A S C : String) (s : LstateA)
    (zf : Bool) (hfD : frame D = none) (hfA : frame A = none) (hfS : frame S = none)
    (hfC : frame C = none)
    {va vb : BitVec 64} (hA : s.reg.getW A 64 = some va) (hS : s.reg.getW S 64 = some vb) :
    fstepA frame (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C], .reg none) s zf
      = (regBit s.reg C).map fun vc =>
          ({ s with reg := (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc },
            zf) := by
  cases hc : s.reg.getW C 1 with
  | some vc =>
    rw [regBit_of_getW1 hc]
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, readReg_of_getW hA, hS, hc, withALUFlags,
      aluFlagOp?, cellA?, slotCarry?, slotImm?, slotCmov?, hfD, hfA, hfS, hfC]
  | none =>
    have hw : wordA frame s A = some va := by simp [wordA, hfA, hA]
    have hw' : wordA frame s S = some vb := by simp [wordA, hfS, hS]
    have hb : bitA frame s C = regBit s.reg C := bitA_of_none hfC s
    cases hr : regBit s.reg C <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, readReg_of_getW hA, hS, hc,
      carryArgs?, wideArgs?, cellA?, slotCarry?, slotImm?, slotCmov?, hfD, hfA,
      hfS, hfC, bitStepA, hw, hw', hb, hr]

/-- The address machine steps `ADCXHI:64 O, A, S, C` on registers by writing the one-bit
    `carryOutBit` of the 64-bit values of `A`, `S` and the bit of `C` (`regBit`) to `O`. -/
theorem fstepA_adcxhi (frame : String → Option (BitVec 64)) (O A S C : String) (s : LstateA)
    (zf : Bool) (hfO : frame O = none) (hfA : frame A = none) (hfS : frame S = none)
    (hfC : frame C = none) {va vb : BitVec 64} (hA : s.reg.getW A 64 = some va) (hS : s.reg.getW S 64 = some vb) :
    fstepA frame (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C], .reg none) s zf
      = (regBit s.reg C).map fun vc =>
          ({ s with reg := (s.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc },
            zf) := by
  cases hc : s.reg.getW C 1 with
  | some vc =>
    rw [regBit_of_getW1 hc]
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, readReg_of_getW hA, hS, hc,
      withALUFlags, aluFlagOp?, cellA?, slotCarry?, slotImm?, slotCmov?,
      hfO, hfA, hfS, hfC]
  | none =>
    have hw : wordA frame s A = some va := by simp [wordA, hfA, hA]
    have hw' : wordA frame s S = some vb := by simp [wordA, hfS, hS]
    have hb : bitA frame s C = regBit s.reg C := bitA_of_none hfC s
    cases hr : regBit s.reg C <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, readReg_of_getW hA, hS, hc,
      carryArgs?, wideArgs?, cellA?, slotCarry?, slotImm?, slotCmov?,
      hfO, hfA, hfS, hfC, bitStepA, hw, hw', hb, hr]

/-! ## 5. The machine steps of the carry chain -/

/-- `bt $0, %c` writes bit `0` of `c` to the carry flag and nothing else. -/
theorem evalInstrA_bt0 (sa : AState) (c : String) :
    (evalInstrA sa (.bt c (.imm 0))).regs = sa.regs
      ∧ (evalInstrA sa (.bt c (.imm 0))).mem = sa.mem
      ∧ (evalInstrA sa (.bt c (.imm 0))).flags.cf = some ((sa.regs c).getLsbD 0) := by
  refine ⟨rfl, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩
  simp [evalInstrA, evalInstr, x86_BT, wbit, AState.view, JOperand.eval]

/-- `adcx %s, %d` writes the word of `x86_ADCX` to `d` and its carry to the carry flag. -/
theorem evalInstrA_adcx (sa : AState) (d s : String) :
    (evalInstrA sa (.adcx d (.reg s))).regs = (fun r => if r = d then
        (x86_ADCX (sa.regs d) (sa.regs s) (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (evalInstrA sa (.adcx d (.reg s))).mem = sa.mem
      ∧ (evalInstrA sa (.adcx d (.reg s))).flags.cf
        = (x86_ADCX (sa.regs d) (sa.regs s) (sa.flags.cf.getD false)).1 := by
  refine ⟨?_, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩ <;>
    simp [evalInstrA, evalInstr, AState.view, JOperand.eval, JState.flagB]

/-- `setc %o` writes `1` or `0` to `o` by the carry flag, and keeps the flags. -/
theorem evalInstrA_setc (sa : AState) (o : String) :
    (evalInstrA sa (.setc o)).regs = (fun r => if r = o then
        (if sa.flags.cf.getD false then 1 else 0) else sa.regs r)
      ∧ (evalInstrA sa (.setc o)).mem = sa.mem
      ∧ (evalInstrA sa (.setc o)).flags = sa.flags := by
  refine ⟨rfl, evalInstrA_mem_of_noWriteB sa _ rfl, rfl⟩

/-- The word of `addCarryWord` is the word of `waddcarry` at the carry-in bit. -/
theorem addCarryWord_eq (va vb : BitVec 64) (vc : BitVec 1) :
    VIR.JasminDialect.addCarryWord va vb vc = (waddcarry va vb (vc.getLsbD 0)).2 := by
  rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
    simp [VIR.JasminDialect.addCarryWord, waddcarry, BitVec.ofNat_add]

/-- The bit of `carryOutBit` is the carry of `waddcarry` at the carry-in bit. -/
theorem carryOutBit_eq (va vb : BitVec 64) (vc : BitVec 1) :
    VIR.JasminDialect.carryOutBit va vb vc
      = if (waddcarry va vb (vc.getLsbD 0)).1 then 1 else 0 := by
  rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
    simp [VIR.JasminDialect.carryOutBit, waddcarry, ge_iff_le]

/-! ## 6. The carry arms -/

/-- A carry instruction of a physical body. -/
inductive CArm where
  /-- `ADCX:64 D, A, S, C`: `D := A + S + C` with the one-bit carry-in `C`. -/
  | adcx (D A S C : String)
  /-- `ADCXHI:64 O, A, S, C`: `O :=` the one-bit carry-out of `A + S + C`. -/
  | adcxhi (O A S C : String)

/-- The instruction of a carry arm. -/
def CArm.instr : CArm → LinstrR
  | .adcx D A S C => .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]
  | .adcxhi O A S C => .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]

/-- The byte pieces of a carry arm. -/
def CArm.pieces : CArm → List (List (BitVec 8) × JInstr 64)
  | .adcx D A S C =>
      (if A = D then [] else [(encAluRRw 1 0x89 (gpNumU D) (gpNumU A),
          .mov (phys D) (.reg (phys A)))])
        ++ [(encBtImm 1 (gpNumU C) 0, .bt (phys C) (.imm 0)),
          (ScalarEncoder.encAdxCarry 0x66 (gpNumU D) (gpNumU S), .adcx (phys D) (.reg (phys S)))]
  | .adcxhi O _ _ _ => [(encSetccMovzx 0x92 (gpNumU O), .setc (phys O))]

/-- The machine instructions of a carry arm. -/
def CArm.js (c : CArm) : List (JInstr 64) := c.pieces.map Prod.snd

/-- **The conditions of a carry arm**: general-purpose operands, a carry-in other than the
    two word sources, and, when the copy of `A` into `D` is laid down, a destination other
    than `S` and `C`, which the copy would overwrite before they are read. -/
def CArm.ok : CArm → Bool
  | .adcx D A S C => gpOk D && gpOk A && gpOk S && gpOk C && A != C && S != C
      && (A == D || (D != S && D != C))
  | .adcxhi O A S C => gpOk O && gpOk A && gpOk S && gpOk C && A != C && S != C

/-- **The bytes of a carry arm.** -/
theorem CArm.bytes (P : Params) (c : CArm) (h : c.ok = true) :
    encodeLopn P.frame P.spillW c.instr P.qsaveB = c.pieces.flatMap Prod.fst
      ∧ ∀ q ∈ c.pieces, PieceDec q := by
  cases c with
  | adcx D A S C =>
    simp only [CArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hD, hA⟩, hS⟩, hC⟩, -⟩, -⟩, -⟩ := h
    refine ⟨?_, ?_⟩
    · rw [CArm.instr, encodeLopn_adcx3 _ _ _ _ _ _ _ hD hA hS hC]
      by_cases hAD : A = D <;> simp [CArm.pieces, hAD]
    · intro q hq
      simp only [CArm.pieces, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        at hq
      rcases hq with hq | rfl | rfl
      · by_cases hAD : A = D
        · simp [hAD] at hq
        · simp only [hAD, ite_false, List.mem_singleton] at hq
          subst hq
          exact fun rest => decodeLinstr_movRR _ _ rest (gpNumU_lt_16 D) (gpNumU_lt_16 A)
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact pieceDec_adcx _ _ (gpNumU_lt_16 D) (gpNumU_lt_16 S)
  | adcxhi O A S C =>
    simp only [CArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hO, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨by simp [CArm.instr, CArm.pieces, encodeLopn_adcxhi3 _ _ _ _ _ _ _ hO], ?_⟩
    intro q hq
    simp only [CArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_setc _ (gpNumU_lt_16 O)

/-- The computed shape of a carry arm's instruction decodes to its machine instructions. -/
theorem CArm.shape_ops {P : Params} {c : CArm} (h : c.ok = true) {sh : DShape}
    (hs : shapeOf P c.instr = some sh) : sh.ops' = c.js := by
  obtain ⟨hb, hp⟩ := c.bytes P h
  cases c <;> exact shapeOf_lopn_ops _ hb hp hs

/-- A write of `v` to the machine register of `D`, against a write to `D` that `ACorrW`
    relates to `v`, preserves `ACorrW` when the memories still agree outside the red-zone
    word. -/
theorem ACorrW.writeN {rsp : BitVec 64} {sa sa' : AState} {s s' : LstateA}
    (h : ACorrW rsp sa s) {D : String} (hD : gpOk D = true) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = phys D then v else sa.regs r)
    (hmem : ∀ x, ¬ InRange8 (redW rsp) x → s'.mem x = sa'.mem x)
    (hlvm : ∀ r, r ≠ D → s'.reg.lvm r = s.reg.lvm r)
    (hcell : s'.reg.getW D 64 = some v
      ∨ (∃ b : BitVec 1, s'.reg.lvm D = ⟨1, b⟩ ∧ v = b.setWidth 64)
      ∨ NarrowCell (s'.reg.lvm D) v) :
    ACorrW rsp sa' s' where
  regs r hr := by
    by_cases hrD : r = D
    · subst hrD
      rw [hregs, ite_eq_left rfl]
      exact hcell
    · rw [hregs, ite_eq_right (fun e => hrD (phys_inj hr hD e))]
      have hl := hlvm r hrD
      have hg : s'.reg.getW r 64 = s.reg.getW r 64 := by unfold LstateN.getW; rw [hl]
      rw [hg, hl]
      exact h.regs r hr
  sp := by rw [hregs, ite_eq_right (fun e => (gpFacts hD).physNe e.symm)]; exact h.sp
  mem := hmem

/-- `ACorrW.writeN` with the written cell at width `64` or `1`. -/
theorem ACorrW.write {rsp : BitVec 64} {sa sa' : AState} {s s' : LstateA}
    (h : ACorrW rsp sa s) {D : String} (hD : gpOk D = true) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = phys D then v else sa.regs r)
    (hmem : ∀ x, ¬ InRange8 (redW rsp) x → s'.mem x = sa'.mem x)
    (hlvm : ∀ r, r ≠ D → s'.reg.lvm r = s.reg.lvm r)
    (hcell : s'.reg.getW D 64 = some v ∨ ∃ b : BitVec 1, s'.reg.lvm D = ⟨1, b⟩ ∧ v = b.setWidth 64) :
    ACorrW rsp sa' s' :=
  h.writeN hD v hregs hmem hlvm (hcell.elim Or.inl fun hb => Or.inr (Or.inl hb))

/-- The carry flag of the machine holds the carry-out of `A + S + C` on the words and the
    carry-in bit (`bitA`) of the address state at the frame `frame`. -/
def CarryAt (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA)
    (A S C : String) : Prop :=
  ∃ co, sa.flags.cf = some co ∧ ∀ va vb vc, wordA frame s A = some va →
    wordA frame s S = some vb → bitA frame s C = some vc → (waddcarry va vb (vc.getLsbD 0)).1 = co

/-- A 64-bit general-purpose name under `ACorrW` reads its machine register. -/
theorem ACorrW.wide {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    {r : String} (hr : gpOk r = true) (hw : (s.reg.lvm r).1 = 64) :
    s.reg.getW r 64 = some (sa.regs (phys r)) := by
  rcases h.regs r hr with hg | ⟨b, hb, -⟩ | hn
  · exact hg
  · rw [hb] at hw
    simp at hw
  · rcases hn.width with h' | h' <;> omega

/-- A name read at width `1` under `ACorrW` holds a bit its machine register zero-extends. -/
theorem ACorrW.bit {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    {r : String} (hr : gpOk r = true) {vc : BitVec 1} (hc : s.reg.getW r 1 = some vc) :
    sa.regs (phys r) = vc.setWidth 64 := by
  have hl := getW_eq_some_iff.1 hc
  rcases h.regs r hr with hg | ⟨b, hb, hm⟩ | hn
  · have := getW_eq_some_iff.1 hg
    rw [hl] at this
    simp at this
  · rw [hl] at hb
    obtain rfl := eq_of_heq (Sigma.mk.inj hb).2
    exact hm
  · have hw := hn.width
    rw [hl] at hw
    simp at hw

/-- A name whose bit (`regBit`) is `vc` under `ACorrW` holds the zero-extension of `vc` in its
    machine register. -/
theorem ACorrW.bitR {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    {r : String} (hr : gpOk r = true) {vc : BitVec 1} (hc : regBit s.reg r = some vc) :
    sa.regs (phys r) = vc.setWidth 64 := by
  rcases regBit_some hc with hl | hl
  · exact h.bit hr (getW_eq_some_iff.2 hl)
  · have e := h.wide hr (by rw [hl])
    rw [getW_eq_some_iff.2 hl] at e
    exact (Option.some.inj e).symm

/-- **The carry-chain add.** From `ACorrW`, with `A` and `S` at width `64`, the address-machine
    step of `ADCX:64 D, A, S, C` is matched by `bt $0, C; adcx S, D` (after the copy of `A`
    into `D`): the registers end related by `ACorrW`, the zero flag is kept, and, when `D` is
    none of `A`, `S`, `C`, the machine carry flag holds the carry-out of the add on the
    values of the result state. -/
theorem sim_adcx (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (CArm.adcx D A S C).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : (s.reg.lvm A).1 = 64) (hwS : (s.reg.lvm S).1 = 64)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((CArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (CArm.adcx D A S C).js) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          CarryAt (frameP P rsp) (aMachine.runBlock sa (CArm.adcx D A S C).js) s' A S C) := by
  simp only [CArm.ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hA⟩, hS⟩, hC⟩, -⟩, -⟩, hal⟩ := h
  set va := sa.regs (phys A) with hva
  set vb := sa.regs (phys S) with hvb
  have hgA := hc.wide hA hwA
  have hgS := hc.wide hS hwS
  rw [CArm.instr, fstepA_adcx3 _ D A S C s zf (frameP_gp hD) (frameP_gp hA) (frameP_gp hS)
    (frameP_gp hC) hgA hgS] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  set bit := vc.getLsbD 0 with hbit
  -- the machine run, up to the copy of `A` into `D`
  obtain ⟨sa1, hrun, h1D, h1S, h1C, h1r, h1f, h1m⟩ : ∃ sa1 : AState,
      aMachine.runBlock sa (CArm.adcx D A S C).js
        = evalInstrA (evalInstrA sa1 (.bt (phys C) (.imm 0))) (.adcx (phys D) (.reg (phys S)))
      ∧ sa1.regs (phys D) = va ∧ sa1.regs (phys S) = vb ∧ sa1.regs (phys C) = vc.setWidth 64
      ∧ (∀ r, r ≠ phys D → sa1.regs r = sa.regs r) ∧ sa1.flags = sa.flags
      ∧ sa1.mem = sa.mem := by
    by_cases hAD : A = D
    · subst hAD
      exact ⟨sa, by simp [CArm.js, CArm.pieces]; rfl, rfl, rfl, hmC, fun _ _ => rfl, rfl, rfl⟩
    · obtain ⟨hDS, hDC⟩ := hal.resolve_left hAD
      have r1 : ∀ r, (evalInstrA sa (.mov (phys D) (.reg (phys A)))).regs r
          = if r = phys D then sa.regs (phys A) else sa.regs r := fun r => rfl
      refine ⟨evalInstrA sa (.mov (phys D) (.reg (phys A))), ?_, ?_, ?_, ?_, ?_, rfl,
        evalInstrA_mem_of_noWriteB sa _ rfl⟩
      · simp [CArm.js, CArm.pieces, hAD]; rfl
      · rw [r1, ite_eq_left rfl]
      · rw [r1, ite_eq_right (fun e => hDS (phys_inj hS hD e).symm)]
      · rw [r1, ite_eq_right (fun e => hDC (phys_inj hC hD e).symm)]; exact hmC
      · intro r hr; rw [r1, ite_eq_right hr]
  obtain ⟨r2, m2, c2⟩ := evalInstrA_bt0 sa1 (phys C)
  obtain ⟨r3, m3, c3⟩ := evalInstrA_adcx (evalInstrA sa1 (.bt (phys C) (.imm 0))) (phys D) (phys S)
  have hcf2 : (evalInstrA sa1 (.bt (phys C) (.imm 0))).flags.cf.getD false = bit := by
    rw [c2, h1C]
    simp [hbit]
  set co := (waddcarry va vb bit).1 with hco
  have hword : (x86_ADCX va vb bit).2 = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [addCarryWord_eq]; rfl
  rw [hrun]
  refine ⟨hc.write hD (VIR.JasminDialect.addCarryWord va vb vc) (fun r => ?_) (fun x hx => ?_)
    (fun r hr => ?_) ?_, rfl, fun hDA hDS hDC => ⟨co, ?_, fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · simp only [r3, r2, hcf2, h1D, h1S, hword]
    split
    · rfl
    · rename_i hne; exact h1r r hne
  · rw [m3, m2, h1m]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · left
    exact getW_setReg_nextPcN s.reg D D _ |>.trans (ite_eq_left rfl)
  · rw [c3, r2, hcf2, h1D, h1S]; rfl
  · simp only [wordA, frameP_gp hA, frameP_gp hS] at ha hb
    rw [bitA_of_none (frameP_gp hC)] at hcc
    have eA : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW A 64
        = some va := by rw [getW_setReg_nextPcN, ite_eq_right (Ne.symm hDA)]; exact hgA
    have eS : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW S 64
        = some vb := by rw [getW_setReg_nextPcN, ite_eq_right (Ne.symm hDS)]; exact hgS
    have eC : regBit (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc C
        = some vc := by
      rw [regBit_of_lvm (r' := s.reg) (by simp [LstateN.nextPc, LstateN.setReg, Ne.symm hDC])]
      exact hgc
    have := ha.symm.trans eA
    have := hb.symm.trans eS
    have := hcc.symm.trans eC
    simp_all

/-- **The carry-out binding.** From `ACorrW`, with `A` and `S` at width `64` and the machine
    carry flag holding the carry-out of `A + S + C`, the address-machine step of
    `ADCXHI:64 O, A, S, C`, which writes the one-bit carry-out to `O`, is matched by
    `setc O`: the registers end related by `ACorrW`, and the zero flag and the machine flags
    are kept. -/
theorem sim_adcxhi (P : Params) (rsp : BitVec 64) (O A S C : String)
    (h : (CArm.adcxhi O A S C).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : (s.reg.lvm A).1 = 64) (hwS : (s.reg.lvm S).1 = 64)
    (hcy : CarryAt (frameP P rsp) sa s A S C) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((CArm.adcxhi O A S C).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (CArm.adcxhi O A S C).js) s' ∧ zf' = zf
      ∧ (aMachine.runBlock sa (CArm.adcxhi O A S C).js).flags = sa.flags := by
  simp only [CArm.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hO, hA⟩, hS⟩, hC⟩, -⟩, -⟩ := h
  have hgA := hc.wide hA hwA
  have hgS := hc.wide hS hwS
  rw [CArm.instr, fstepA_adcxhi _ O A S C s zf (frameP_gp hO) (frameP_gp hA) (frameP_gp hS)
    (frameP_gp hC) hgA hgS] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨co, hcf, hco⟩ := hcy
  have hco' := hco _ _ _ (by simp only [wordA, frameP_gp hA]; exact hgA)
    (by simp only [wordA, frameP_gp hS]; exact hgS) (by rw [bitA_of_none (frameP_gp hC)]; exact hgc)
  obtain ⟨r1, m1, f1⟩ := evalInstrA_setc sa (phys O)
  have hrun : aMachine.runBlock sa (CArm.adcxhi O A S C).js = evalInstrA sa (.setc (phys O)) := rfl
  rw [hrun]
  refine ⟨hc.write hO (if co then 1 else 0) (fun r => ?_) (fun x hx => ?_) (fun r hr => ?_) ?_,
    rfl, f1⟩
  · rw [r1, hcf]; rfl
  · rw [m1]; exact hc.mem x hx
  · show (s.reg.setReg O _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    refine ⟨VIR.JasminDialect.carryOutBit (sa.regs (phys A)) (sa.regs (phys S)) vc, ?_, ?_⟩
    · show (if O = O then _ else _) = _
      rw [ite_eq_left rfl]
    · rw [carryOutBit_eq, hco']
      cases co <;> decide

/-! ## 7. The cell arms -/

/-- The encoder's parse of a `mem.<B>.<off>` name is the address machine's, with the base
    read as a register number. -/
theorem parseMemName_cellParts (n : String) :
    parseMemName n = (cellParts? n).map fun p => (gpNumU p.1, Int.ofNat p.2) := by
  unfold parseMemName cellParts?
  split
  · generalize List.span (fun x => x != '.') (List.drop 4 n.toList) = p
    rcases p with ⟨base, _ | ⟨c, off⟩⟩
    · rfl
    · by_cases hc : c = '.'
      · subst hc
        simp only
        cases natOfDigits? off <;> rfl
      · simp [hc]
  · rfl

/-- The encoder's resolution of a `mem.<B>.<off>` name is the address machine's parse,
    with the base read as a register number when it is a general-purpose name. -/
theorem parseMemNameGp_cellParts (n : String) :
    parseMemNameGp n = (cellParts? n).bind fun p =>
      if isGpName p.1 then some (gpNumU p.1, Int.ofNat p.2) else none := by
  unfold parseMemNameGp cellParts?
  split
  · generalize List.span (fun x => x != '.') (List.drop 4 n.toList) = p
    rcases p with ⟨base, _ | ⟨c, off⟩⟩
    · rfl
    · by_cases hc : c = '.'
      · subst hc
        simp only
        cases natOfDigits? off <;> rfl
      · simp [hc]
  · rfl

/-- A whole-word access of a cell `[B + off]` of a physical body. -/
inductive MArm where
  /-- `LOAD:64 D, n` with `n` the cell `[B + off]`. -/
  | ldm (D n B : String) (off : Nat)
  /-- `STORE:64 n, S` with `n` the cell `[B + off]`. -/
  | stm (n B : String) (off : Nat) (S : String)
  /-- `MOV:64 n, S` with `n` the cell `[B + off]`. -/
  | stv (n B : String) (off : Nat) (S : String)
  /-- `MOV:64 D, n` with `n` the cell `[B + off]` and `D` no cell name. -/
  | ldv (D n B : String) (off : Nat)

/-- The instruction of a cell arm. -/
def MArm.instr : MArm → LinstrR
  | .ldm D n _ _ => .Lopn [.reg D] "LOAD:64" [.reg n]
  | .stm n _ _ S => .Lopn [.reg n] "STORE:64" [.reg S]
  | .stv n _ _ S => .Lopn [.reg n] "MOV:64" [.reg S]
  | .ldv D n _ _ => .Lopn [.reg D] "MOV:64" [.reg n]

/-- The byte pieces of a cell arm: `mov off(%B), %D` and `mov %S, off(%B)`. -/
def MArm.pieces : MArm → List (List (BitVec 8) × JInstr 64)
  | .ldm D _ B off => [(encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off),
      .loadMem (phys D) (phys B) (Int.ofNat off))]
  | .stm _ B off S => [(encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off),
      .storeMem (phys B) (Int.ofNat off) (.reg (phys S)))]
  | .stv _ B off S => [(encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off),
      .storeMem (phys B) (Int.ofNat off) (.reg (phys S)))]
  | .ldv D _ B off => [(encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off),
      .loadMem (phys D) (phys B) (Int.ofNat off))]

/-- The machine instructions of a cell arm. -/
def MArm.js (m : MArm) : List (JInstr 64) := m.pieces.map Prod.snd

/-- **The conditions of a cell arm**: the cell name parses to the base and offset of the arm,
    general-purpose register and base, and an offset with a signed 32-bit displacement. -/
def MArm.ok : MArm → Bool
  | .ldm D n B off => cellParts? n == some (B, off) && gpOk D && gpOk B
      && dispOk32 (Int.ofNat off)
  | .stm n B off S => cellParts? n == some (B, off) && gpOk S && gpOk B
      && dispOk32 (Int.ofNat off)
  | .stv n B off S => cellParts? n == some (B, off) && gpOk S && gpOk B
      && dispOk32 (Int.ofNat off)
  | .ldv D n B off => cellParts? n == some (B, off) && gpOk D && gpOk B
      && dispOk32 (Int.ofNat off)

/-- The cell arm of an instruction. -/
def classifyM : LinstrR → Option MArm
  | .Lopn [.reg d] o [.reg n] =>
      if o = "LOAD:64" then (cellParts? n).map fun p => .ldm d n p.1 p.2
      else if o = "STORE:64" then (cellParts? d).map fun p => .stm d p.1 p.2 n
      else if o = "MOV:64" then
        match cellParts? d with
        | some p => some (.stv d p.1 p.2 n)
        | none => (cellParts? n).map fun p => .ldv d n p.1 p.2
      else none
  | _ => none

theorem classifyM_instr {i : LinstrR} {m : MArm} (h : classifyM i = some m) : m.instr = i := by
  unfold classifyM at h
  split at h
  · split_ifs at h with h1 h2 h3
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; subst h1; rfl
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; subst h2; rfl
    · subst h3
      split at h
      · cases h; rfl
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
  · cases h

/-- `mov off(%b), %d` with a signed 32-bit displacement. -/
theorem pieceDec_loadMem (d b : Nat) (off : Int) (hd : d < 16) (hb : b < 16)
    (h : dispOk32 off = true) :
    PieceDec (encMemMovw 1 0x8b d b off,
      .loadMem (SailX86Decoder.regName d) (SailX86Decoder.regName b) off) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_loadMem32 (canonAlloc ()) (SailX86Decoder.regName d)
    (SailX86Decoder.regName b) off rest h
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, regOf_canon hd, regOf_canon hb,
    gpNum_regName hd, gpNum_regName hb, LprogJInstrBytesAgree.encMemMovw_one] using e

/-- A cell name is no frame-slot name. -/
theorem notSlot_of_cell {n : String} {p : String × Nat} (h : cellParts? n = some p) :
    isSpillOrQsave n = false ∧ ∀ F W qB, spillQsaveOff F W n qB = none := by
  unfold cellParts? at h
  split at h
  · rename_i hp
    unfold hasPrefix at hp
    rw [List.isPrefixOf_iff_prefix] at hp
    obtain ⟨t, ht⟩ := hp
    have hk : hasPrefix n "k." = false := by
      unfold hasPrefix; rw [← ht]; simp [List.isPrefixOf]
    have hq : hasPrefix n "qsave." = false := by
      unfold hasPrefix; rw [← ht]; simp [List.isPrefixOf]
    exact ⟨by simp [isSpillOrQsave, hk, hq], fun F W qB => by simp [spillQsaveOff, hk, hq]⟩
  · cases h

/-- `LOAD:64 D, n` with `n` the cell `[B + off]` and `D`, `B` general-purpose. -/
theorem encodeLopn_ldm (F W : Nat) (D n B : String) (off : Nat) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hD : gpOk D = true) (hB : gpOk B = true) :
    encodeLopn F W (.Lopn [.reg D] "LOAD:64" [.reg n]) qB
      = encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off) := by
  have fD := gpFacts hD
  obtain ⟨-, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemNameGp n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemNameGp_cellParts, hn]; simp [(gpFacts hB).isGp]
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fD.off, fD.notMem,
    fD.isGp, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memSrcOp, adxPrefix]

/-- `STORE:64 n, S` with `n` the cell `[B + off]` and `S`, `B` general-purpose. -/
theorem encodeLopn_stm (F W : Nat) (n B : String) (off : Nat) (S : String) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hS : gpOk S = true) (hB : gpOk B = true) :
    encodeLopn F W (.Lopn [.reg n] "STORE:64" [.reg S]) qB
      = encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off) := by
  have fS := gpFacts hS
  obtain ⟨-, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemNameGp n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemNameGp_cellParts, hn]; simp [(gpFacts hB).isGp]
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fS.off, fS.notMem,
    fS.isGp, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memDstOp, adxPrefix]

/-- `MOV:64 n, S` with `n` the cell `[B + off]` and `S`, `B` general-purpose: the bytes of
    `STORE:64 n, S`. -/
theorem encodeLopn_stv (F W : Nat) (n B : String) (off : Nat) (S : String) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hS : gpOk S = true) (hB : gpOk B = true) :
    encodeLopn F W (.Lopn [.reg n] "MOV:64" [.reg S]) qB
      = encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off) := by
  have fS := gpFacts hS
  obtain ⟨-, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemNameGp n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemNameGp_cellParts, hn]; simp [(gpFacts hB).isGp]
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fS.off, fS.notMem,
    fS.isGp, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memDstOp, adxPrefix]

/-- `MOV:64 D, n` with `n` the cell `[B + off]` and `D`, `B` general-purpose: the bytes of
    `LOAD:64 D, n`. -/
theorem encodeLopn_ldv (F W : Nat) (D n B : String) (off : Nat) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hD : gpOk D = true) (hB : gpOk B = true) :
    encodeLopn F W (.Lopn [.reg D] "MOV:64" [.reg n]) qB
      = encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off) := by
  have fD := gpFacts hD
  obtain ⟨-, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemNameGp n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemNameGp_cellParts, hn]; simp [(gpFacts hB).isGp]
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fD.off, fD.notMem,
    fD.isGp, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memSrcOp, adxPrefix]

/-- **The bytes of a cell arm.** -/
theorem MArm.bytes (P : Params) (m : MArm) (h : m.ok = true) :
    encodeLopn P.frame P.spillW m.instr P.qsaveB = m.pieces.flatMap Prod.fst
      ∧ ∀ q ∈ m.pieces, PieceDec q := by
  cases m with
  | ldm D n B off =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hD⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_ldm _ _ _ _ _ _ _ hn hD hB], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_loadMem _ _ _ (gpNumU_lt_16 D) (gpNumU_lt_16 B) hd
  | stm n B off S =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hS⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_stm _ _ _ _ _ _ _ hn hS hB], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_storeMem _ _ _ (gpNumU_lt_16 S) (gpNumU_lt_16 B) hd
  | stv n B off S =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hS⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_stv _ _ _ _ _ _ _ hn hS hB], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_storeMem _ _ _ (gpNumU_lt_16 S) (gpNumU_lt_16 B) hd
  | ldv D n B off =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hD⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_ldv _ _ _ _ _ _ _ hn hD hB], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_loadMem _ _ _ (gpNumU_lt_16 D) (gpNumU_lt_16 B) hd

/-- The computed shape of a cell arm's instruction decodes to its machine instruction. -/
theorem MArm.shape_ops {P : Params} {m : MArm} (h : m.ok = true) {sh : DShape}
    (hs : shapeOf P m.instr = some sh) : sh.ops' = m.js := by
  obtain ⟨hb, hp⟩ := m.bytes P h
  cases m <;> exact shapeOf_lopn_ops _ hb hp hs

/-- A cell arm is no compare arm of `DecodePrintedAddr`. -/
theorem MArm.cmpArm_false {m : MArm} (h : m.ok = true) :
    (classifyA m.instr).any cmpArmB = false := by
  cases m with
  | stv n B off S =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    have hn : gpOk n = false := by
      cases hg : gpOk n
      · rfl
      · rw [cellParts?_gp hg] at h; simp at h
    simp [MArm.instr, classifyA, cmpArmB, isMovM, hn]
  | ldv D n B off =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hc, hD⟩, -⟩, -⟩ := h
    have hn : gpOk n = false := by
      cases hg : gpOk n
      · rfl
      · rw [cellParts?_gp hg] at hc; cases hc
    simp [MArm.instr, classifyA, cmpArmB, isMovM, hD, hn]
  | _ => simp [MArm.instr, classifyA, cmpArmB, Option.any_map, isMovM]

/-- **The cell load.** From `ACorrW`, with the base `B` at width `64` and the eight bytes at
    the cell address disjoint from the red-zone word, the address-machine step of
    `LOAD:64 D, n` is matched by `mov off(%B), %D`. -/
theorem sim_ldm (P : Params) (rsp : BitVec 64) (D n B : String) (off : Nat)
    (h : (MArm.ldm D n B off).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64)
    (hsafe : ∀ p, s.reg.getW B 64 = some p → Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off))
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.ldm D n B off).js) s' ∧ zf' = zf := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := h
  have hgB := hc.wide hB hwB
  rw [MArm.instr, fstepA_ldm _ hn hgB] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  set a := sa.regs (phys B) + BitVec.ofNat 64 off with ha
  have hrd : read64 s.mem a = read64 sa.mem a := read64_eq_of_agree hc.mem (hsafe _ hgB)
  obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (phys D) (phys B) (Int.ofNat off)
  have hofs : BitVec.ofInt 64 (Int.ofNat off) = BitVec.ofNat 64 off := BitVec.ofInt_natCast _ _
  have hrun : aMachine.runBlock sa (MArm.ldm D n B off).js
      = evalInstrA sa (.loadMem (phys D) (phys B) (Int.ofNat off)) := rfl
  rw [hrun]
  refine ⟨hc.write hD (read64 s.mem a) (fun r => by rw [hregs, hofs, hrd]) (fun x hx => ?_)
    (fun r hr => ?_) (Or.inl ?_), rfl⟩
  · rw [hmem]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · exact getW_setReg_nextPcN s.reg D D _ |>.trans (ite_eq_left rfl)

/-- **The cell store.** From `ACorrW`, with the base `B` and the source `S` at width `64`,
    the address-machine step of `STORE:64 n, S` is matched by `mov %S, off(%B)`. -/
theorem sim_stm (P : Params) (rsp : BitVec 64) (n B : String) (off : Nat) (S : String)
    (h : (MArm.stm n B off S).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64) (hwS : (s.reg.lvm S).1 = 64)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.stm n B off S).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.stm n B off S).js) s' ∧ zf' = zf := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := h
  have hgB := hc.wide hB hwB
  have hgS := hc.wide hS hwS
  rw [MArm.instr, fstepA_stm _ hn hgB hgS] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hregs, hmem⟩ := evalInstrA_storeMem_eq sa (phys B) (phys S) (Int.ofNat off)
  have hofs : BitVec.ofInt 64 (Int.ofNat off) = BitVec.ofNat 64 off := BitVec.ofInt_natCast _ _
  have hrun : aMachine.runBlock sa (MArm.stm n B off S).js
      = evalInstrA sa (.storeMem (phys B) (Int.ofNat off) (.reg (phys S))) := rfl
  rw [hrun]
  refine ⟨⟨fun r hr => ?_, by rw [hregs]; exact hc.sp, fun x hx => ?_⟩, rfl⟩
  · rw [hregs]
    have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · show write64 s.mem _ _ x = _
    rw [hmem, hofs]
    exact agree_write64 hc.mem _ _ x hx

/-- **The move into a cell.** From `ACorrW`, with the base `B` and the source `S` at width
    `64`, the address-machine step of `MOV:64 n, S` is matched by `mov %S, off(%B)`. -/
theorem sim_stv (P : Params) (rsp : BitVec 64) (n B : String) (off : Nat) (S : String)
    (h : (MArm.stv n B off S).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64) (hwS : (s.reg.lvm S).1 = 64)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.stv n B off S).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.stv n B off S).js) s' ∧ zf' = zf := by
  have hok := h
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := h
  rw [MArm.instr, fstepA_movStm _ hn (hc.wide hB hwB) (hc.wide hS hwS)] at hst
  have hst' : fstepA (frameP P rsp) ((MArm.stm n B off S).instr, .reg none) s zf
      = some (s', zf') := by
    rw [MArm.instr, fstepA_stm _ hn (hc.wide hB hwB) (hc.wide hS hwS)]; exact hst
  exact sim_stm P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst'

/-- **The move out of a cell.** From `ACorrW`, with the base `B` at width `64` and the eight
    bytes at the cell address disjoint from the red-zone word, the address-machine step of
    `MOV:64 D, n` is matched by `mov off(%B), %D`. -/
theorem sim_ldv (P : Params) (rsp : BitVec 64) (D n B : String) (off : Nat)
    (h : (MArm.ldv D n B off).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64)
    (hsafe : ∀ p, s.reg.getW B 64 = some p → Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off))
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.ldv D n B off).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.ldv D n B off).js) s' ∧ zf' = zf := by
  have hok : (MArm.ldm D n B off).ok = true := h
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := h
  have hgB := hc.wide hB hwB
  rw [MArm.instr, fstepA_movLdm _ hn (cellParts?_gp hD) hgB] at hst
  have hst' : fstepA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s zf
      = some (s', zf') := by
    rw [MArm.instr, fstepA_ldm _ hn hgB]; exact hst
  exact sim_ldm P rsp D n B off hok sa s zf hc hwB hsafe s' zf' hst'

/-! ## 8. The carry arms with frame-slot operands -/

/-- A slot name is no cell name and no general-purpose name. -/
theorem slot_facts {x : String} {F W qB : Nat} {off : Int}
    (h : spillQsaveOff F W x qB = some off) :
    isSpillOrQsave x = true ∧ parseMemName x = none ∧ gpOk x = false := by
  unfold spillQsaveOff at h
  have hpre : hasPrefix x "k." = true ∨ hasPrefix x "qsave." = true := by
    split at h
    · exact Or.inl ‹_›
    · split at h
      · exact Or.inr ‹_›
      · cases h
  refine ⟨by simp [isSpillOrQsave, hpre], ?_, ?_⟩
  · unfold parseMemName
    rcases hpre with hp | hp <;>
    · unfold hasPrefix at hp ⊢
      rw [List.isPrefixOf_iff_prefix] at hp
      obtain ⟨t, ht⟩ := hp
      rw [← ht]
      simp [List.isPrefixOf]
  · cases hg : gpOk x
    · rfl
    · have hm := mem_gpList hg
      simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [hasPrefix] at hpre

/-- The four scratch candidates of a spilled-destination add are not all among three names. -/
theorem scratch_exists (A S C : String) :
    (["RAX", "RBX", "RCX", "RDX"].filter fun r => !([A, S, C].contains r)) ≠ [] := by
  intro h
  rw [List.filter_eq_nil_iff] at h
  have h1 := h "RAX" (by simp)
  have h2 := h "RBX" (by simp)
  have h3 := h "RCX" (by simp)
  have h4 := h "RDX" (by simp)
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_true',
    Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq] at h1 h2 h3 h4
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;>
    (subst_vars; simp_all (config := { decide := true }))

/-- The scratch register of a spilled-destination add: the first of `RAX`, `RBX`, `RCX`,
    `RDX` none of `A`, `S`, `C` names, as the encoder and the printer pick it. -/
def scratchS (A S C : String) : String :=
  match ["RAX", "RBX", "RCX", "RDX"].filter fun r => !([A, S, C].contains r) with
  | r :: _ => r
  | [] => "RDX"

/-- An operand of a carry arm: a general-purpose name, or a frame slot whose offset has a
    signed 32-bit displacement and whose eight bytes are disjoint from the red-zone word. -/
def kOk (P : Params) (x : String) : Bool :=
  gpOk x || (isSpillOrQsave x && match spillQsaveOff P.frame P.spillW x P.qsaveB with
    | some off => dispOk32 off && sepB cmovRedZone off
    | none => false)

/-- A carry instruction with a frame-slot operand. -/
inductive SArm where
  /-- `ADCX:64 D, A, S, C` with a frame slot among `D`, `A`, `S`. -/
  | adcx (D A S C : String)
  /-- `ADCXHI:64 O, A, S, C` with a frame slot among `A`, `S`, `C`. -/
  | adcxhi (O A S C : String)
  /-- `ADCX:64 D, A, S, C` with the carry-in `C` a frame slot. -/
  | adcxc (D A S C : String)

/-- The instruction of a slot carry arm. -/
def SArm.instr : SArm → LinstrR
  | .adcx D A S C => .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]
  | .adcxhi O A S C => .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]
  | .adcxc D A S C => .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]

/-- The test of a slot carry-in `C` in the scratch `acc`: the save of the scratch in the
    red-zone word, the reload of the frame word of `C` and `bt $0` of the scratch. -/
def cPre (P : Params) (C : String) (acc : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(encRspMem 1 0x89 acc cmovRedZone,
      .storeMem "%rsp" cmovRedZone (.reg (SailX86Decoder.regName acc))),
   (encRspMem 1 0x8b acc (slotOff P C),
      .loadMem (SailX86Decoder.regName acc) "%rsp" (slotOff P C)),
   (encBtImm 1 acc 0, .bt (SailX86Decoder.regName acc) (.imm 0))]

/-- The restore of the scratch `acc` from the red-zone word. -/
def cRst (acc : Nat) : List (BitVec 8) × JInstr 64 :=
  (encRspMem 1 0x8b acc cmovRedZone, .loadMem (SailX86Decoder.regName acc) "%rsp" cmovRedZone)

/-- The copy of `A` into the accumulator `acc` of the add into `D`: a reload from the slot
    of `A`, nothing when `A` is the accumulator `D`, a register copy otherwise. -/
def sMv (P : Params) (D A : String) (acc : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if isSpillOrQsave A then
    [(encRspMem 1 0x8b acc (slotOff P A),
      .loadMem (SailX86Decoder.regName acc) "%rsp" (slotOff P A))]
  else if A = D ∧ acc = gpNumU D then []
  else [(encAluRRw 1 0x89 acc (gpNumU A), .mov (SailX86Decoder.regName acc) (.reg (phys A)))]

/-- The add of `S` into the accumulator `acc`: `adcx` from the slot of `S` or from `S`. -/
def sAd (P : Params) (S : String) (acc : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if isSpillOrQsave S then
    [(encAdxRspMem 0x66 acc (slotOff P S),
      .adcxMem (SailX86Decoder.regName acc) "%rsp" (slotOff P S))]
  else [(ScalarEncoder.encAdxCarry 0x66 acc (gpNumU S),
      .adcx (SailX86Decoder.regName acc) (.reg (phys S)))]

/-- The byte pieces of a slot carry arm. -/
def SArm.pieces (P : Params) : SArm → List (List (BitVec 8) × JInstr 64)
  | .adcx D A S C =>
      let bt := (encBtImm 1 (gpNumU C) 0, JInstr.bt (phys C) (.imm 0))
      if isSpillOrQsave D then
        let acc := gpNumU (scratchS A S C)
        bt :: (encRspMem 1 0x89 acc cmovRedZone,
            .storeMem "%rsp" cmovRedZone (.reg (SailX86Decoder.regName acc)))
          :: (sMv P D A acc ++ sAd P S acc
            ++ [(encRspMem 1 0x89 acc (slotOff P D),
                  .storeMem "%rsp" (slotOff P D) (.reg (SailX86Decoder.regName acc))),
                (encRspMem 1 0x8b acc cmovRedZone,
                  .loadMem (SailX86Decoder.regName acc) "%rsp" cmovRedZone)])
      else sMv P D A (gpNumU D) ++ bt :: sAd P S (gpNumU D)
  | .adcxhi O _ _ _ => [(encSetccMovzx 0x92 (gpNumU O), .setc (phys O))]
  | .adcxc D A S C =>
      let acc := gpNumU (scratchS A S C)
      if isSpillOrQsave D then
        cPre P C acc ++ sMv P D A acc ++ sAd P S acc
          ++ [(encRspMem 1 0x89 acc (slotOff P D),
                .storeMem "%rsp" (slotOff P D) (.reg (SailX86Decoder.regName acc))), cRst acc]
      else cPre P C acc ++ cRst acc :: (sMv P D A (gpNumU D) ++ sAd P S (gpNumU D))

/-- The machine instructions of a slot carry arm. -/
def SArm.js (P : Params) (c : SArm) : List (JInstr 64) := (c.pieces P).map Prod.snd

/-- **The conditions of a slot carry arm**: general-purpose or well-placed slot operands with a
    slot among them; for the add with a register carry-in, a carry-in other than the word
    sources; for the carry-out binding, a carry-in other than the word sources and a
    general-purpose destination; for the add with a slot carry-in, a well-placed slot
    carry-in; and, for a register destination of an add with the copy of `A` laid down, a
    destination other than `S` and `C`. -/
def SArm.ok (P : Params) : SArm → Bool
  | .adcx D A S C => gpOk C && A != C && S != C && kOk P D && kOk P A && kOk P S
      && (isSpillOrQsave D || isSpillOrQsave A || isSpillOrQsave S)
      && (isSpillOrQsave D || (A == D && gpOk A) || (D != S && D != C))
  | .adcxhi O A S C => gpOk O && kOk P C && A != C && S != C && kOk P A && kOk P S
      && (isSpillOrQsave A || isSpillOrQsave S || isSpillOrQsave C)
  | .adcxc D A S C => isSpillOrQsave C && kOk P C && kOk P D && kOk P A && kOk P S
      && (isSpillOrQsave D || (A == D && gpOk A) || D != S)

theorem kOk_cases {P : Params} {x : String} (h : kOk P x = true) :
    gpOk x = true ∨ ∃ off, spillQsaveOff P.frame P.spillW x P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
  unfold kOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact Or.inl h
  · right
    split at h
    · rename_i off hoff
      simp only [Bool.and_eq_true] at h
      exact ⟨off, hoff, h.1, h.2⟩
    · cases h

/-- At a name accepted by `kOk`, `frameP` is the frame address of the spill or save offset. -/
theorem frameP_of_kOk {P : Params} {rsp : BitVec 64} {x : String} (h : kOk P x = true) :
    frameP P rsp x
      = (spillQsaveOff P.frame P.spillW x P.qsaveB).map fun o => rsp + BitVec.ofInt 64 o := by
  rcases kOk_cases h with hg | ⟨off, hoff, -⟩
  · rw [frameP_gp hg, (gpFacts hg).off]
    rfl
  · simp [frameP, hoff]

/-- The facts of an operand the encoder reads: a general-purpose name, or a slot at its
    offset. -/
theorem opnd_facts {P : Params} {x : String} (h : kOk P x = true) :
    parseMemName x = none ∧ (isSpillOrQsave x = false ∨ ∃ off,
      spillQsaveOff P.frame P.spillW x P.qsaveB = some off ∧ isSpillOrQsave x = true
        ∧ slotOff P x = off) := by
  rcases kOk_cases h with hg | ⟨off, hoff, -, -⟩
  · exact ⟨(gpFacts hg).notMem, Or.inl (gpFacts hg).notSlot⟩
  · obtain ⟨h1, h2, -⟩ := slot_facts hoff
    exact ⟨h2, Or.inr ⟨off, hoff, h1, by simp [slotOff, hoff]⟩⟩

/-- The encoder's choice of the scratch register is `scratchS`. -/
theorem scratch_filter (A S C : String) :
    ["RAX", "RBX", "RCX", "RDX"].filter (fun r => !([A, S, C].contains r))
      = scratchS A S C :: (["RAX", "RBX", "RCX", "RDX"].filter
          (fun r => !([A, S, C].contains r))).tail := by
  unfold scratchS
  have hne := scratch_exists A S C
  revert hne
  cases ["RAX", "RBX", "RCX", "RDX"].filter (fun r => !([A, S, C].contains r)) with
  | nil => intro h; exact absurd rfl h
  | cons r rs => intro _; rfl

/-- **The bytes of a slot carry add.** -/
theorem encodeLopn_sadcx (P : Params) (D A S C : String) (h : (SArm.adcx D A S C).ok P = true) :
    encodeLopn P.frame P.spillW (SArm.adcx D A S C).instr P.qsaveB
      = ((SArm.adcx D A S C).pieces P).flatMap Prod.fst := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, -⟩, hal⟩ := h
  have fC := gpFacts hC
  obtain ⟨hDm, hDk⟩ := opnd_facts hD
  obtain ⟨hAm, hAk⟩ := opnd_facts hA
  obtain ⟨hSm, hSk⟩ := opnd_facts hS
  have hst : stripWidthTag "ADCX:64" = "ADCX" := by decide +kernel
  have hpx : adxPrefix "ADCX" = some 0x66 := rfl
  have hw : LprogBytes.rexW (LprogAsmPrinter.mnemWidth "ADCX:64") = 1 := by decide +kernel
  have hfC := fC.notSlot
  have hmC := fC.notMem
  have hsc := scratch_filter A S C
  rcases hDk with hDs | ⟨oD, hoD, hDs, hsD⟩ <;> rcases hAk with hAs | ⟨oA, hoA, hAs, hsA⟩ <;>
    rcases hSk with hSs | ⟨oS, hoS, hSs, hsS⟩ <;>
    simp (config := { decide := true }) [encodeLopn, SArm.instr, SArm.pieces, sMv, sAd, *]
  all_goals first
    | (by_cases hAD : A = D <;> simp [hAD] <;> done)
    | (split
       · rename_i heq
         exact absurd heq (by simpa using scratch_exists A S C)
       · rename_i r tl heq
         have hr : scratchS A S C = r := by simp [scratchS, heq]
         rw [hr]
         by_cases hAD : A = D
         · subst hAD; simp_all [cmovRedZone]
         · simp [hAD, cmovRedZone])

/-- **The bytes of a carry add with a slot carry-in.** -/
theorem encodeLopn_sadcxc (P : Params) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) :
    encodeLopn P.frame P.spillW (SArm.adcxc D A S C).instr P.qsaveB
      = ((SArm.adcxc D A S C).pieces P).flatMap Prod.fst := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hCs, hC⟩, hD⟩, hA⟩, hS⟩, hal⟩ := h
  obtain ⟨hCm, hCk⟩ := opnd_facts hC
  obtain ⟨oC, hoC, -, hsC⟩ := hCk.resolve_left (by simp [hCs])
  obtain ⟨hDm, hDk⟩ := opnd_facts hD
  obtain ⟨hAm, hAk⟩ := opnd_facts hA
  obtain ⟨hSm, hSk⟩ := opnd_facts hS
  have hst : stripWidthTag "ADCX:64" = "ADCX" := by decide +kernel
  have hpx : adxPrefix "ADCX" = some 0x66 := rfl
  have hw : LprogBytes.rexW (LprogAsmPrinter.mnemWidth "ADCX:64") = 1 := by decide +kernel
  have hsc := scratch_filter A S C
  rcases hDk with hDs | ⟨oD, hoD, hDs, hsD⟩ <;> rcases hAk with hAs | ⟨oA, hoA, hAs, hsA⟩ <;>
    rcases hSk with hSs | ⟨oS, hoS, hSs, hsS⟩ <;>
    simp (config := { decide := true }) [encodeLopn, SArm.instr, SArm.pieces, cPre, cRst, sMv,
      sAd, *]
  all_goals
    split
    · rename_i heq
      exact absurd heq (by simpa using scratch_exists A S C)
    · rename_i r tl heq
      have hr : scratchS A S C = r := by simp [scratchS, heq]
      rw [hr]
      by_cases hAD : A = D
      · subst hAD; simp_all [cmovRedZone]
      · simp [hAD, cmovRedZone]

/-- `adcx off(%rsp), %d` with a signed 32-bit displacement. -/
theorem pieceDec_adcxRsp (d : Nat) (off : Int) (hd : d < 16) (h : dispOk32 off = true) :
    PieceDec (encAdxRspMem 0x66 d off,
      .adcxMem (SailX86Decoder.regName d) "%rsp" off) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_adcxMem32 (canonAlloc ()) (SailX86Decoder.regName d) "%rsp" off rest h
  have hrsp : AsmPrinter.regOf (canonAlloc ()) "%rsp" = "%rsp" := by decide
  have hg4 : ScalarEncoder.gpNum "%rsp" = 4 := by decide
  have heq : encAdxRspMem 0x66 d off
      = ScalarEncoder.encodeJInstr (canonAlloc ()) (.adcxMem (SailX86Decoder.regName d) "%rsp" off) := by
    simp only [ScalarEncoder.encodeJInstr, regOf_canon hd, gpNum_regName hd, hrsp, hg4,
      encAdxRspMem, ScalarEncoder.memTail]
    split_ifs <;> simp_all (config := { decide := true })
  rw [heq]
  have h4 : SailX86Decoder.regName 4 = "%rsp" := rfl
  simpa [renameJ, nameOf, regOf_canon hd, hrsp, gpNum_regName hd, hg4, h4] using e

/-- The pieces of the copy of a well-placed operand `A` into the accumulator decode. -/
theorem sMv_pieceDec {P : Params} {D A : String} (hA : kOk P A = true) (acc : Nat)
    (hacc : acc < 16) : ∀ q ∈ sMv P D A acc, PieceDec q := by
  intro q hq
  simp only [sMv] at hq
  split at hq
  · simp only [List.mem_singleton] at hq
    subst hq
    rcases kOk_cases hA with hg | ⟨off, hoff, hd, -⟩
    · simp_all [(gpFacts hg).notSlot]
    · intro rest
      rw [show slotOff P A = off by simp [slotOff, hoff]]
      exact decodeLinstr_rspLoad acc off rest hacc hd
  · split at hq
    · cases hq
    · simp only [List.mem_singleton] at hq
      subst hq
      exact fun rest => decodeLinstr_movRR _ _ rest hacc (gpNumU_lt_16 A)

/-- The pieces of the add of a well-placed operand `S` into the accumulator decode. -/
theorem sAd_pieceDec {P : Params} {S : String} (hS : kOk P S = true) (acc : Nat)
    (hacc : acc < 16) : ∀ q ∈ sAd P S acc, PieceDec q := by
  intro q hq
  simp only [sAd] at hq
  split at hq
  · simp only [List.mem_singleton] at hq
    subst hq
    rcases kOk_cases hS with hg | ⟨off, hoff, hd, -⟩
    · simp_all [(gpFacts hg).notSlot]
    · rw [show slotOff P S = off by simp [slotOff, hoff]]
      exact pieceDec_adcxRsp acc off hacc hd
  · simp only [List.mem_singleton] at hq
    subst hq
    exact pieceDec_adcx _ _ hacc (gpNumU_lt_16 S)

/-- The displacement of a well-placed slot is a signed 32-bit one. -/
theorem kOk_disp {P : Params} {x : String} (hk : kOk P x = true) (hs : isSpillOrQsave x = true) :
    dispOk32 (slotOff P x) = true := by
  rcases kOk_cases hk with hg | ⟨off, hoff, hd, -⟩
  · simp [(gpFacts hg).notSlot] at hs
  · simpa [slotOff, hoff] using hd

/-- **The bytes of a slot carry arm.** -/
theorem SArm.bytes (P : Params) (c : SArm) (h : c.ok P = true) :
    encodeLopn P.frame P.spillW c.instr P.qsaveB = (c.pieces P).flatMap Prod.fst
      ∧ ∀ q ∈ c.pieces P, PieceDec q := by
  cases c with
  | adcx D A S C =>
    refine ⟨encodeLopn_sadcx P D A S C h, ?_⟩
    simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hC, -⟩, -⟩, hD⟩, hA⟩, hS⟩, -⟩, -⟩ := h
    have hmv : ∀ acc, acc < 16 → ∀ q ∈ sMv P D A acc, PieceDec q := by
      intro acc hacc q hq
      simp only [sMv] at hq
      split at hq
      · simp only [List.mem_singleton] at hq
        subst hq
        rcases kOk_cases hA with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · intro rest
          rw [show slotOff P A = off by simp [slotOff, hoff]]
          exact decodeLinstr_rspLoad acc off rest hacc hd
      · split at hq
        · cases hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact fun rest => decodeLinstr_movRR _ _ rest hacc (gpNumU_lt_16 A)
    have had : ∀ acc, acc < 16 → ∀ q ∈ sAd P S acc, PieceDec q := by
      intro acc hacc q hq
      simp only [sAd] at hq
      split at hq
      · simp only [List.mem_singleton] at hq
        subst hq
        rcases kOk_cases hS with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · rw [show slotOff P S = off by simp [slotOff, hoff]]
          exact pieceDec_adcxRsp acc off hacc hd
      · simp only [List.mem_singleton] at hq
        subst hq
        exact pieceDec_adcx _ _ hacc (gpNumU_lt_16 S)
    intro q hq
    simp only [SArm.pieces] at hq
    split at hq
    · rename_i hDs
      have hacc := gpNumU_lt_16 (scratchS A S C)
      have hdD : dispOk32 (slotOff P D) = true := by
        rcases kOk_cases hD with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · simpa [slotOff, hoff] using hd
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | ((hq | hq) | rfl | rfl)
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact fun rest => decodeLinstr_rspStore _ cmovRedZone rest hacc (by decide)
      · exact hmv _ hacc q hq
      · exact had _ hacc q hq
      · exact fun rest => decodeLinstr_rspStore _ _ rest hacc hdD
      · exact fun rest => decodeLinstr_rspLoad _ cmovRedZone rest hacc (by decide)
    · simp only [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq
      · exact hmv _ (gpNumU_lt_16 D) q hq
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact had _ (gpNumU_lt_16 D) q hq
  | adcxhi O A S C =>
    simp only [SArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hO, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨by simp [SArm.instr, SArm.pieces, encodeLopn_adcxhi3 _ _ _ _ _ _ _ hO], ?_⟩
    intro q hq
    simp only [SArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_setc _ (gpNumU_lt_16 O)
  | adcxc D A S C =>
    refine ⟨encodeLopn_sadcxc P D A S C h, ?_⟩
    simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hCs, hC⟩, hD⟩, hA⟩, hS⟩, -⟩ := h
    have hacc := gpNumU_lt_16 (scratchS A S C)
    have hpre : ∀ q ∈ cPre P C (gpNumU (scratchS A S C)), PieceDec q := by
      intro q hq
      simp only [cPre, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact fun rest => decodeLinstr_rspStore _ cmovRedZone rest hacc (by decide)
      · exact fun rest => decodeLinstr_rspLoad _ _ rest hacc (kOk_disp hC hCs)
      · exact pieceDec_bt _ hacc
    have hrst : PieceDec (cRst (gpNumU (scratchS A S C))) :=
      fun rest => decodeLinstr_rspLoad _ cmovRedZone rest hacc (by decide)
    intro q hq
    simp only [SArm.pieces] at hq
    split at hq
    · rename_i hDs
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with ((hq | hq) | hq) | rfl | rfl
      · exact hpre q hq
      · exact sMv_pieceDec hA _ hacc q hq
      · exact sAd_pieceDec hS _ hacc q hq
      · exact fun rest => decodeLinstr_rspStore _ _ rest hacc (kOk_disp hD hDs)
      · exact hrst
    · simp only [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq | hq
      · exact hpre q hq
      · exact hrst
      · exact sMv_pieceDec hA _ (gpNumU_lt_16 D) q hq
      · exact sAd_pieceDec hS _ (gpNumU_lt_16 D) q hq

/-- The computed shape of a slot carry arm's instruction decodes to its machine
    instructions. -/
theorem SArm.shape_ops {P : Params} {c : SArm} (h : c.ok P = true) {sh : DShape}
    (hs : shapeOf P c.instr = some sh) : sh.ops' = c.js P := by
  obtain ⟨hb, hp⟩ := c.bytes P h
  cases c <;> exact shapeOf_lopn_ops _ hb hp hs

/-- The machine word of an operand: the word at its frame address for a slot, its register
    otherwise. -/
def valM (P : Params) (rsp : BitVec 64) (sa : AState) (x : String) : BitVec 64 :=
  if isSpillOrQsave x then read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P x))
  else sa.regs (phys x)

theorem sepB_disj {off : Int} (h : sepB cmovRedZone off = true) (rsp : BitVec 64) :
    Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 off) := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact disjoint8_add_ofInt rsp cmovRedZone off h.1 h.2

/-- An operand of a slot carry arm reads, on the address machine, its machine word. -/
theorem wordA_valM {P : Params} {rsp : BitVec 64} {sa : AState} {s : LstateA}
    (hc : ACorrW rsp sa s) {x : String} (hk : kOk P x = true)
    (hw : gpOk x = true → (s.reg.lvm x).1 = 64) :
    wordA (frameP P rsp) s x = some (valM P rsp sa x) := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, hsep⟩
  · simp [wordA, frameP_gp hg, valM, (gpFacts hg).notSlot, hc.wide hg (hw hg)]
  · obtain ⟨hs, -, -⟩ := slot_facts hoff
    simp only [wordA, frameP, hoff, Option.map_some, valM, hs, ite_true,
      show slotOff P x = off by simp [slotOff, hoff]]
    rw [read64_eq_of_agree hc.mem (sepB_disj hsep rsp)]

/-- `adcx off(%b), %d` writes the word of `x86_ADCX` to `d` and its carry to the carry flag. -/
theorem evalInstrA_adcxMem (sa : AState) (d b : String) (off : Int) :
    (evalInstrA sa (.adcxMem d b off)).regs = (fun r => if r = d then
        (x86_ADCX (sa.regs d) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))
          (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (evalInstrA sa (.adcxMem d b off)).mem = sa.mem
      ∧ (evalInstrA sa (.adcxMem d b off)).flags.cf
        = (x86_ADCX (sa.regs d) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))
            (sa.flags.cf.getD false)).1 := by
  refine ⟨?_, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩ <;>
    simp [evalInstrA, evalInstr, AState.view, JState.flagB, JState.load]

/-- The copy of `A` into the accumulator `acc`, when it is laid down, writes the machine word
    of `A` to `acc` and keeps the memory and the flags. -/
theorem run_sMv (P : Params) (rsp : BitVec 64) (D A : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp)
    (hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ acc = gpNumU D)) :
    (∀ r, (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).regs r
        = if r = SailX86Decoder.regName acc then valM P rsp sa A else sa.regs r)
      ∧ (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).mem = sa.mem
      ∧ (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).flags = sa.flags := by
  unfold sMv
  split
  · rename_i hs
    obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (SailX86Decoder.regName acc) "%rsp"
      (slotOff P A)
    refine ⟨fun r => ?_, hmem, rfl⟩
    show (evalInstrA sa _).regs r = _
    rw [hregs, hsp]
    simp [valM, hs]
  · rename_i hs
    have hlay' := hlay.resolve_left (by simp [hs])
    rw [ite_eq_right hlay']
    refine ⟨fun r => ?_, evalInstrA_mem_of_noWriteB sa _ rfl, rfl⟩
    show (evalInstrA sa _).regs r = _
    simp [valM, hs]
    rfl

/-- The add of `S` into the accumulator `acc` writes the word of `x86_ADCX` of the
    accumulator, the machine word of `S` and the carry flag to `acc`, and its carry to the
    carry flag. -/
theorem run_sAd (P : Params) (rsp : BitVec 64) (S : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) :
    (∀ r, (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).regs r
        = if r = SailX86Decoder.regName acc then
            (x86_ADCX (sa.regs (SailX86Decoder.regName acc)) (valM P rsp sa S)
              (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).mem = sa.mem
      ∧ (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).flags.cf
        = (x86_ADCX (sa.regs (SailX86Decoder.regName acc)) (valM P rsp sa S)
            (sa.flags.cf.getD false)).1 := by
  unfold sAd
  split
  · rename_i hs
    obtain ⟨hr, hm, hf⟩ := evalInstrA_adcxMem sa (SailX86Decoder.regName acc) "%rsp" (slotOff P S)
    refine ⟨fun r => ?_, hm, ?_⟩
    · show (evalInstrA sa _).regs r = _
      rw [hr, hsp]
      simp [valM, hs]
    · show (evalInstrA sa _).flags.cf = _
      rw [hf, hsp]
      simp [valM, hs]
  · rename_i hs
    obtain ⟨hr, hm, hf⟩ := evalInstrA_adcx sa (SailX86Decoder.regName acc) (phys S)
    refine ⟨fun r => ?_, hm, ?_⟩
    · show (evalInstrA sa _).regs r = _
      rw [hr]
      simp [valM, hs]
    · show (evalInstrA sa _).flags.cf = _
      rw [hf]
      simp [valM, hs]

/-- A slot operand has a frame address. -/
theorem kOk_frame {P : Params} {x : String} (hk : kOk P x = true)
    (hs : isSpillOrQsave x = true) (rsp : BitVec 64) : (frameP P rsp x).isSome = true := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, -⟩
  · simp [(gpFacts hg).notSlot] at hs
  · simp [frameP, hoff]

/-- Some operand of a slot carry arm is a slot, which the address machine sees. -/
theorem slot_seen {P : Params} {D A S : String} (hD : kOk P D = true) (hA : kOk P A = true)
    (hS : kOk P S = true)
    (h : isSpillOrQsave D = true ∨ isSpillOrQsave A = true ∨ isSpillOrQsave S = true)
    (rsp : BitVec 64) :
    ((frameP P rsp D).isSome || (frameP P rsp A).isSome || (frameP P rsp S).isSome) = true := by
  rcases h with h | h | h <;> simp [kOk_frame _ h rsp, *]

/-- A word the address machine reads off a name other than `D` survives a write to `D` that
    keeps the memory. -/
theorem wordA_setReg {frame : String → Option (BitVec 64)} {s : LstateA} {D x : String}
    (hx : x ≠ D) {w : Nat} (v : BitVec w) :
    wordA frame { s with reg := (s.reg.setReg D v).nextPc } x = wordA frame s x := by
  unfold wordA
  split
  · rfl
  · show (s.reg.setReg D v).nextPc.getW x 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hx]

/-- **The slot carry add into a register.** From `ACorrW`, the address-machine step of
    `ADCX:64 D, A, S, C` with `D` a register and a slot among `A`, `S` is matched by the
    reload or copy of `A` into `D`, `bt $0, C` and `adcx` from the slot or register `S`. -/
theorem sim_sadcx_reg (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcx D A S C).ok P = true) (hDg : gpOk D = true) (sa : AState) (s : LstateA)
    (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' A S C) := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, hsl0⟩, hal⟩ := h
  have hDs : isSpillOrQsave D = false := (gpFacts hDg).notSlot
  have hfD : frameP P rsp D = none := frameP_gp hDg
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  rw [SArm.instr, fstepA_adcxSlot _ D A S C s zf (slot_seen hD hA hS (by simp_all) rsp) hA' hS'
    (frameP_gp hC)] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  set bit := vc.getLsbD 0 with hbit
  have hCD : C ≠ D := by
    intro e; subst e
    rcases hal with (hal | ⟨rfl, -⟩) | ⟨-, hal⟩
    · simp [hDs] at hal
    · exact hAC rfl
    · exact hal rfl
  have hsp := hc.sp
  -- the machine run: the copy of `A`, `bt`, the add
  have hjs : (SArm.adcx D A S C).js P
      = (sMv P D A (gpNumU D)).map Prod.snd ++ (.bt (phys C) (.imm 0)
        :: (sAd P S (gpNumU D)).map Prod.snd) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append]
  have hpD : SailX86Decoder.regName (gpNumU D) = phys D := rfl
  set sa1 := aMachine.runBlock sa ((sMv P D A (gpNumU D)).map Prod.snd) with hsa1
  obtain ⟨r1D, r1o, m1, f1⟩ : sa1.regs (phys D) = va ∧ (∀ r, r ≠ phys D → sa1.regs r = sa.regs r)
      ∧ sa1.mem = sa.mem ∧ sa1.flags = sa.flags := by
    by_cases hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU D = gpNumU D)
    · obtain ⟨hr, hm, hf⟩ := run_sMv P rsp D A (gpNumU D) sa hsp hlay
      refine ⟨by rw [hr, hpD, ite_eq_left rfl], fun r hr' => by rw [hr, hpD, ite_eq_right hr'], hm, hf⟩
    · simp only [not_or, Bool.not_eq_true, not_not] at hlay
      obtain ⟨hAs, rfl, -⟩ := hlay
      have he : sMv P A A (gpNumU A) = [] := by simp [sMv, hAs]
      rw [hsa1, he]
      exact ⟨by simp [hva, valM, hAs], fun _ _ => rfl, rfl, rfl⟩
  set sa2 := evalInstrA sa1 (.bt (phys C) (.imm 0)) with hsa2
  obtain ⟨r2, m2, c2⟩ : sa2.regs = sa1.regs ∧ sa2.mem = sa1.mem
      ∧ sa2.flags.cf = some ((sa1.regs (phys C)).getLsbD 0) := evalInstrA_bt0 sa1 (phys C)
  have hC1 : sa1.regs (phys C) = vc.setWidth 64 := by
    rw [r1o _ (fun e => hCD (phys_inj hC hDg e)), hmC]
  have hcf2 : sa2.flags.cf.getD false = bit := by
    rw [c2, hC1]; simp [hbit]
  have hsp2 : sa2.regs "%rsp" = rsp := by
    rw [r2, r1o _ (fun e => (gpFacts hDg).physNe e.symm), hsp]
  have hvb2 : valM P rsp sa2 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp [valM, hSs, m2, m1, hvb]
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, ite_false, hvb, r2]
      by_cases hSD : S = D
      · subst hSD
        rcases hal with (hal | ⟨rfl, -⟩) | ⟨hal, -⟩
        · simp [hDs] at hal
        · rw [r1D]; simp [hva, valM, (gpFacts hDg).notSlot]
        · exact absurd rfl hal
      · rw [r1o _ (fun e => hSD (phys_inj hSg hDg e))]
  obtain ⟨r3, m3, c3⟩ := run_sAd P rsp S (gpNumU D) sa2 hsp2
  rw [hpD, r2, r1D, hvb2, hcf2] at r3 c3
  have hword : (x86_ADCX va vb bit).2 = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [addCarryWord_eq]; rfl
  rw [hjs, RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_cons]
  change ACorrW rsp (aMachine.runBlock sa2 _) _ ∧ _
  refine ⟨hc.write hDg (VIR.JasminDialect.addCarryWord va vb vc) (fun r => ?_) (fun x hx => ?_)
    (fun r hr => ?_) ?_, rfl, fun hDA hDS hDC => ⟨(waddcarry va vb bit).1, ?_,
      fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [r3, ← hword]
    split
    · rfl
    · rename_i hne; exact r1o _ hne
  · rw [m3, m2, m1]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · left
    exact getW_setReg_nextPcN s.reg D D _ |>.trans (ite_eq_left rfl)
  · exact c3
  · rw [wordA_setReg (Ne.symm hDA)] at ha
    rw [wordA_setReg (Ne.symm hDS)] at hb
    rw [bitA_of_none (frameP_gp hC)] at hcc
    have eC : regBit (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc C
        = some vc := by
      rw [regBit_of_lvm (r' := s.reg) (by simp [LstateN.nextPc, LstateN.setReg, Ne.symm hDC])]
      exact hgc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans eC
    simp_all

/-- The scratch register is one of `RAX`, `RBX`, `RCX`, `RDX` and none of `A`, `S`, `C`. -/
theorem scratchS_spec (A S C : String) :
    gpOk (scratchS A S C) = true ∧ scratchS A S C ≠ A ∧ scratchS A S C ≠ S
      ∧ scratchS A S C ≠ C := by
  have hmem : scratchS A S C ∈ ["RAX", "RBX", "RCX", "RDX"].filter
      (fun r => !([A, S, C].contains r)) := by
    rw [scratch_filter A S C]; exact List.mem_cons_self
  rw [List.mem_filter] at hmem
  obtain ⟨h1, h2⟩ := hmem
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_true',
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h2
  refine ⟨?_, fun e => h2.1 e, fun e => h2.2.1 e, fun e => h2.2.2 e⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h <;> rw [h] <;> decide

/-- A word the address machine reads off a name whose frame address is disjoint from `ad`
    survives a store at `ad`. -/
theorem wordA_write {frame : String → Option (BitVec 64)} {s : LstateA} {ad : BitVec 64}
    {x : String} (hx : ∀ ax, frame x = some ax → Disjoint8 ad ax) (v : BitVec 64) :
    wordA frame { s with reg := s.reg.nextPc, mem := write64 s.mem ad v } x = wordA frame s x := by
  unfold wordA
  split
  · rename_i ax hax
    simp only [Option.some.injEq]
    exact read64_write64_of_disjoint _ _ _ _ (hx ax hax)
  · exact LstateN.getW_nextPc _ _ _

/-- `mov %x, off(%b)` keeps the registers and the flags. -/
theorem evalInstrA_storeMem_flags (sa : AState) (b x : String) (off : Int) :
    (evalInstrA sa (.storeMem b off (.reg x))).flags = sa.flags := rfl

/-- `mov off(%b), %d` keeps the flags. -/
theorem evalInstrA_loadMem_flags (sa : AState) (d b : String) (off : Int) :
    (evalInstrA sa (.loadMem d b off)).flags = sa.flags := rfl

/-- **The slot carry add into a slot.** From `ACorrW`, the address-machine step of
    `ADCX:64 D, A, S, C` with `D` a frame slot is matched by `bt $0, C`, the save of the
    scratch in the red-zone word, the reload or copy of `A` into the scratch, `adcx` from the
    slot or register `S`, the store into the slot of `D` and the restore of the scratch. -/
theorem sim_sadcx_slot (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcx D A S C).ok P = true) (hDs : isSpillOrQsave D = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          (isSpillOrQsave A = true → sepB (slotOff P D) (slotOff P A) = true) →
          (isSpillOrQsave S = true → sepB (slotOff P D) (slotOff P S) = true) →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' A S C) := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, -⟩, -⟩ := h
  obtain ⟨offD, hoD, -, hsepD⟩ : ∃ off, spillQsaveOff P.frame P.spillW D P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
    rcases kOk_cases hD with hg | h
    · simp [(gpFacts hg).notSlot] at hDs
    · exact h
  have hsD : slotOff P D = offD := by simp [slotOff, hoD]
  set aD := rsp + BitVec.ofInt 64 offD with haD
  have hfD : frameP P rsp D = some aD := by simp [frameP, hoD, haD]
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  rw [SArm.instr, fstepA_adcxSlot _ D A S C s zf (by simp [hfD]) hA' hS' (frameP_gp hC)] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  set bit := vc.getLsbD 0 with hbit
  have hsp := hc.sp
  obtain ⟨hRg, hRA, hRS, hRC⟩ := scratchS_spec A S C
  set R := SailX86Decoder.regName (gpNumU (scratchS A S C)) with hR
  have hRp : R = phys (scratchS A S C) := rfl
  have hRne : ∀ x, gpOk x = true → x ≠ scratchS A S C → phys x ≠ R := fun x hx hne e =>
    hne (phys_inj hx hRg (e.trans hRp))
  have hRsp : R ≠ "%rsp" := by rw [hRp]; exact (gpFacts hRg).physNe
  have hsepRA : isSpillOrQsave A = true → Disjoint8 (redW rsp)
      (rsp + BitVec.ofInt 64 (slotOff P A)) := fun hs => by
    rcases kOk_cases hA with hg | ⟨off, hoff, -, hsep⟩
    · simp [(gpFacts hg).notSlot] at hs
    · rw [show slotOff P A = off by simp [slotOff, hoff]]; exact sepB_disj hsep rsp
  have hsepRS : isSpillOrQsave S = true → Disjoint8 (redW rsp)
      (rsp + BitVec.ofInt 64 (slotOff P S)) := fun hs => by
    rcases kOk_cases hS with hg | ⟨off, hoff, -, hsep⟩
    · simp [(gpFacts hg).notSlot] at hs
    · rw [show slotOff P S = off by simp [slotOff, hoff]]; exact sepB_disj hsep rsp
  -- the run
  have hjs : (SArm.adcx D A S C).js P
      = .bt (phys C) (.imm 0) :: .storeMem "%rsp" cmovRedZone (.reg R)
        :: ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd
          ++ (sAd P S (gpNumU (scratchS A S C))).map Prod.snd
          ++ [.storeMem "%rsp" (slotOff P D) (.reg R), .loadMem R "%rsp" cmovRedZone]) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append, hR]
  set sa1 := evalInstrA sa (.bt (phys C) (.imm 0)) with hsa1
  obtain ⟨r1, m1, c1⟩ : sa1.regs = sa.regs ∧ sa1.mem = sa.mem
      ∧ sa1.flags.cf = some ((sa.regs (phys C)).getLsbD 0) := evalInstrA_bt0 sa (phys C)
  set sa2 := evalInstrA sa1 (.storeMem "%rsp" cmovRedZone (.reg R)) with hsa2
  obtain ⟨r2, m2⟩ := evalInstrA_storeMem_eq sa1 "%rsp" R cmovRedZone
  rw [← hsa2] at r2 m2
  have f2 : sa2.flags = sa1.flags := evalInstrA_storeMem_flags _ _ _ _
  rw [r1, m1, hsp] at m2
  set old := sa.regs R with hold
  have hsp2 : sa2.regs "%rsp" = rsp := by rw [r2, r1, hsp]
  set sa3 := aMachine.runBlock sa2 ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd)
    with hsa3
  have hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU (scratchS A S C) = gpNumU D) := by
    by_cases hAs : isSpillOrQsave A = true
    · exact Or.inl hAs
    · right; rintro ⟨rfl, -⟩; exact hAs hDs
  obtain ⟨r3, m3, f3⟩ := run_sMv P rsp D A (gpNumU (scratchS A S C)) sa2 hsp2 hlay
  rw [← hsa3] at r3 m3 f3
  have hva3 : valM P rsp sa2 A = va := by
    by_cases hAs : isSpillOrQsave A = true
    · simp only [valM, hAs, ite_true, hva, m2]
      exact read64_write64_of_disjoint _ _ _ _ (hsepRA hAs)
    · have hAg : gpOk A = true := by
        rcases kOk_cases hA with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hAs
      simp only [valM, hAs, Bool.false_eq_true, ite_false, hva, r2, r1]
  set sa4 := aMachine.runBlock sa3 ((sAd P S (gpNumU (scratchS A S C))).map Prod.snd) with hsa4
  have hsp3 : sa3.regs "%rsp" = rsp := by rw [r3, ite_eq_right (Ne.symm hRsp), hsp2]
  obtain ⟨r4, m4, c4⟩ := run_sAd P rsp S (gpNumU (scratchS A S C)) sa3 hsp3
  rw [← hsa4] at r4 m4 c4
  have hvb3 : valM P rsp sa3 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp only [valM, hSs, ite_true, hvb, m3, m2]
      exact read64_write64_of_disjoint _ _ _ _ (hsepRS hSs)
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, ite_false, hvb]
      rw [r3, ite_eq_right (hRne S hSg (Ne.symm hRS)), r2, r1]
  have hcf3 : sa3.flags.cf.getD false = bit := by
    rw [f3, f2, c1, hmC]; simp [hbit]
  rw [show sa3.regs R = va by rw [r3, ite_eq_left rfl, hva3], hvb3, hcf3] at r4 c4
  set res := (x86_ADCX va vb bit).2 with hres
  set sa5 := evalInstrA sa4 (.storeMem "%rsp" (slotOff P D) (.reg R)) with hsa5
  obtain ⟨r5, m5⟩ := evalInstrA_storeMem_eq sa4 "%rsp" R (slotOff P D)
  rw [← hsa5] at r5 m5
  have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, ite_eq_right (Ne.symm hRsp), hsp3]
  rw [hsp4, hsD, r4, ite_eq_left rfl] at m5
  set sa6 := evalInstrA sa5 (.loadMem R "%rsp" cmovRedZone) with hsa6
  obtain ⟨r6, m6⟩ := evalInstrA_loadMem_eq sa5 R "%rsp" cmovRedZone
  rw [← hsa6] at r6 m6
  have hsp5 : sa5.regs "%rsp" = rsp := by rw [r5, hsp4]
  have hDisD : Disjoint8 aD (redW rsp) := by
    have := sepB_disj hsepD rsp
    exact ⟨this.2, this.1⟩
  have hrest : read64 sa5.mem (sa5.regs "%rsp" + BitVec.ofInt 64 cmovRedZone) = old := by
    rw [hsp5, m5, m4, m3, m2]
    show read64 (write64 (write64 sa.mem (redW rsp) old) aD res) (redW rsp) = old
    rw [read64_write64_of_disjoint _ _ _ _ hDisD, read64_write64_same]
  have hrun : aMachine.runBlock sa ((SArm.adcx D A S C).js P) = sa6 := by
    rw [hjs, RInstrSemantics.Machine.runBlock_cons, RInstrSemantics.Machine.runBlock_cons,
      RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_append]
    rfl
  have hword : res = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [hres, addCarryWord_eq]; rfl
  rw [hrun]
  have hregs6 : sa6.regs = sa.regs := by
    funext r
    rw [r6, hrest, r5, r4]
    by_cases hr : r = R
    · subst hr; rw [ite_eq_left rfl]
    · rw [ite_eq_right hr, ite_eq_right hr, r3, ite_eq_right hr, r2, r1]
  have hmem6 : sa6.mem = write64 (write64 sa.mem (redW rsp) old) aD res := by
    rw [m6, m5, m4, m3, m2]; rfl
  refine ⟨⟨fun r hr => ?_, by rw [hregs6]; exact hsp, fun x hx => ?_⟩, rfl,
    fun hDA hDS hDC hsA hsS => ⟨(waddcarry va vb bit).1, ?_, fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [hregs6]
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [LstateN.getW_nextPc]
    exact hc.regs r hr
  · show write64 s.mem aD _ x = _
    rw [hmem6, ← hword]
    refine agree_write64 (fun y hy => ?_) _ _ x hx
    rw [write64_of_not_inRange _ _ _ _ hy]
    exact hc.mem y hy
  · show sa6.flags.cf = _
    rw [evalInstrA_loadMem_flags, evalInstrA_storeMem_flags, c4]
    rfl
  · have hdisA : ∀ ax, frameP P rsp A = some ax → Disjoint8 aD ax := by
      intro ax hax
      simp only [frameP_of_kOk hA, Option.map_eq_some_iff] at hax
      obtain ⟨off, hoff, rfl⟩ := hax
      have hAs := (slot_facts hoff).1
      have hsep := hsA hAs
      rw [hsD, show slotOff P A = off by simp [slotOff, hoff]] at hsep
      simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
      exact disjoint8_add_ofInt rsp offD off hsep.1 hsep.2
    have hdisS : ∀ ax, frameP P rsp S = some ax → Disjoint8 aD ax := by
      intro ax hax
      simp only [frameP_of_kOk hS, Option.map_eq_some_iff] at hax
      obtain ⟨off, hoff, rfl⟩ := hax
      have hSs := (slot_facts hoff).1
      have hsep := hsS hSs
      rw [hsD, show slotOff P S = off by simp [slotOff, hoff]] at hsep
      simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
      exact disjoint8_add_ofInt rsp offD off hsep.1 hsep.2
    rw [wordA_write hdisA] at ha
    rw [wordA_write hdisS] at hb
    rw [bitA_of_none (frameP_gp hC)] at hcc
    have eC : regBit s.reg.nextPc C = some vc := by
      rw [regBit_of_lvm (r' := s.reg) (by simp [LstateN.nextPc])]; exact hgc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans eC
    simp_all

/-- **The slot carry-out binding.** From `ACorrW`, with the machine carry flag holding the
    carry-out of `A + S + C` on the address-machine words, the step of `ADCXHI:64 O, A, S, C`
    with a slot among `A`, `S` is matched by `setc O`: the registers end related by `ACorrW`,
    and the zero flag and the machine flags are kept. -/
theorem sim_sadcxhi (P : Params) (rsp : BitVec 64) (O A S C : String)
    (h : (SArm.adcxhi O A S C).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (hcy : CarryAt (frameP P rsp) sa s A S C)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcxhi O A S C).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)) s' ∧ zf' = zf
      ∧ (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)).flags = sa.flags := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hO, hC⟩, -⟩, -⟩, hA⟩, hS⟩, hsl0⟩ := h
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  have hsl : ((frameP P rsp O).isSome || (frameP P rsp A).isSome
      || (frameP P rsp S).isSome || (frameP P rsp C).isSome) = true := by
    rcases hsl0 with (h | h) | h
    · simp [kOk_frame hA h rsp]
    · simp [kOk_frame hS h rsp]
    · simp [kOk_frame hC h rsp]
  rw [SArm.instr, fstepA_adcxhiSlotBit _ O A S C s zf hsl hA' hS'] at hst
  cases hgc : bitA (frameP P rsp) s C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, frameP_gp hO, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨co, hcf, hco⟩ := hcy
  have hco' := hco _ _ _ hA' hS' hgc
  obtain ⟨r1, m1, f1⟩ := evalInstrA_setc sa (phys O)
  have hrun : aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)
      = evalInstrA sa (.setc (phys O)) := rfl
  rw [hrun]
  refine ⟨hc.write hO (if co then 1 else 0) (fun r => ?_) (fun x hx => ?_) (fun r hr => ?_) ?_,
    rfl, f1⟩
  · rw [r1, hcf]; rfl
  · rw [m1]; exact hc.mem x hx
  · show (s.reg.setReg O _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    refine ⟨VIR.JasminDialect.carryOutBit (valM P rsp sa A) (valM P rsp sa S) vc, ?_, ?_⟩
    · show (if O = O then _ else _) = _
      rw [ite_eq_left rfl]
    · rw [carryOutBit_eq, hco']
      cases co <;> decide

/-- The frame words of `d` and `x` are disjoint when both are slots. -/
def slotSepB (P : Params) (d x : String) : Bool :=
  !(isSpillOrQsave d && isSpillOrQsave x) || sepB (slotOff P d) (slotOff P x)

/-- **The slot carry add.** From `ACorrW`, the address-machine step of `ADCX:64 D, A, S, C`
    with a frame slot among `D`, `A`, `S` is matched by the machine instructions of its slot
    carry arm: the registers end related by `ACorrW`, the zero flag is kept, and, when `D` is
    none of `A`, `S`, `C` and its frame word is disjoint from those of `A` and `S`, the machine
    carry flag holds the carry-out of the add on the words of the result state. -/
theorem sim_sadcx (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcx D A S C).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C → slotSepB P D A = true → slotSepB P D S = true →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' A S C) := by
  by_cases hDs : isSpillOrQsave D = true
  · obtain ⟨h1, h2, h3⟩ := sim_sadcx_slot P rsp D A S C h hDs sa s zf hc hwA hwS s' zf' hst
    refine ⟨h1, h2, fun hDA hDS hDC hsa hss => h3 hDA hDS hDC (fun hAs => ?_) (fun hSs => ?_)⟩
    · simpa [slotSepB, hDs, hAs] using hsa
    · simpa [slotSepB, hDs, hSs] using hss
  · have hD : kOk P D = true := by
      simp only [SArm.ok, Bool.and_eq_true] at h
      exact h.1.1.1.1.2
    have hDg : gpOk D = true := by
      rcases kOk_cases hD with hg | ⟨off, hoff, -, -⟩
      · exact hg
      · exact absurd (slot_facts hoff).1 hDs
    obtain ⟨h1, h2, h3⟩ := sim_sadcx_reg P rsp D A S C h hDg sa s zf hc hwA hwS s' zf' hst
    exact ⟨h1, h2, fun hDA hDS hDC _ _ => h3 hDA hDS hDC⟩

/-! ## 8a. The carry add with a slot carry-in -/

/-- A slot carry-in reads, on the address machine, the low bit of its machine word. -/
theorem bitA_valM {P : Params} {rsp : BitVec 64} {sa : AState} {s : LstateA}
    (hc : ACorrW rsp sa s) {x : String} (hk : kOk P x = true) (hs : isSpillOrQsave x = true) :
    bitA (frameP P rsp) s x = some ((valM P rsp sa x).setWidth 1) := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, hsep⟩
  · simp [(gpFacts hg).notSlot] at hs
  · simp only [bitA, frameP, hoff, Option.map_some, valM, hs, ite_true,
      show slotOff P x = off by simp [slotOff, hoff]]
    rw [read64_eq_of_agree hc.mem (sepB_disj hsep rsp)]

/-- The frame word of a well-placed slot is disjoint from the red-zone word. -/
theorem kOk_sep {P : Params} {x : String} (hk : kOk P x = true) (hs : isSpillOrQsave x = true)
    (rsp : BitVec 64) : Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 (slotOff P x)) := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, hsep⟩
  · simp [(gpFacts hg).notSlot] at hs
  · rw [show slotOff P x = off by simp [slotOff, hoff]]; exact sepB_disj hsep rsp

/-- The machine word of a well-placed operand is kept by a state with the same registers and
    a memory changed only in the red-zone word. -/
theorem valM_red {P : Params} {rsp : BitVec 64} {sa sa' : AState} {x : String}
    (hk : kOk P x = true) (hr : sa'.regs = sa.regs) {v : BitVec 64}
    (hm : sa'.mem = write64 sa.mem (redW rsp) v) : valM P rsp sa' x = valM P rsp sa x := by
  by_cases hs : isSpillOrQsave x = true
  · simp only [valM, hs, ite_true, hm]
    exact read64_write64_of_disjoint _ _ _ _ (kOk_sep hk hs rsp)
  · simp only [valM, hs, Bool.false_eq_true, ite_false, hr]

/-- **The test of a slot carry-in.** The save of the scratch, the reload of the frame word of
    `C` and `bt $0` of the scratch write the frame word to the scratch, save the scratch in the
    red-zone word and set the carry flag to the low bit of the frame word. -/
theorem run_cPre (P : Params) (rsp : BitVec 64) (C : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp)
    (hd : Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 (slotOff P C))) :
    (∀ r, (aMachine.runBlock sa ((cPre P C acc).map Prod.snd)).regs r
        = if r = SailX86Decoder.regName acc then
            read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P C)) else sa.regs r)
      ∧ (aMachine.runBlock sa ((cPre P C acc).map Prod.snd)).mem
        = write64 sa.mem (redW rsp) (sa.regs (SailX86Decoder.regName acc))
      ∧ (aMachine.runBlock sa ((cPre P C acc).map Prod.snd)).flags.cf
        = some ((read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P C))).getLsbD 0) := by
  set R := SailX86Decoder.regName acc with hR
  have hrun : aMachine.runBlock sa ((cPre P C acc).map Prod.snd)
      = evalInstrA (evalInstrA (evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R)))
          (.loadMem R "%rsp" (slotOff P C))) (.bt R (.imm 0)) := rfl
  rw [hrun]
  obtain ⟨r1, m1⟩ := evalInstrA_storeMem_eq sa "%rsp" R cmovRedZone
  set sa1 := evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R))
  obtain ⟨r2, m2⟩ := evalInstrA_loadMem_eq sa1 R "%rsp" (slotOff P C)
  set sa2 := evalInstrA sa1 (.loadMem R "%rsp" (slotOff P C))
  obtain ⟨r3, m3, c3⟩ := evalInstrA_bt0 sa2 R
  have hm1 : sa1.mem = write64 sa.mem (redW rsp) (sa.regs R) := by rw [m1, hsp]; rfl
  have hw : read64 sa1.mem (sa1.regs "%rsp" + BitVec.ofInt 64 (slotOff P C))
      = read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P C)) := by
    rw [r1, hsp, hm1]; exact read64_write64_of_disjoint _ _ _ _ hd
  refine ⟨fun r => ?_, ?_, ?_⟩
  · rw [r3, r2, hw, r1]
  · rw [m3, m2, hm1]
  · rw [c3, r2, ite_eq_left rfl, hw]

/-- **The test of a slot carry-in followed by the restore.** The registers are kept, the
    memory changes in the red-zone word only, and the carry flag holds the low bit of the
    frame word of `C`. -/
theorem run_cTest (P : Params) (rsp : BitVec 64) (C : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) (hacc : SailX86Decoder.regName acc ≠ "%rsp")
    (hd : Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 (slotOff P C))) :
    (aMachine.runBlock sa ((cPre P C acc).map Prod.snd ++ [(cRst acc).2])).regs = sa.regs
      ∧ (aMachine.runBlock sa ((cPre P C acc).map Prod.snd ++ [(cRst acc).2])).mem
        = write64 sa.mem (redW rsp) (sa.regs (SailX86Decoder.regName acc))
      ∧ (aMachine.runBlock sa ((cPre P C acc).map Prod.snd ++ [(cRst acc).2])).flags.cf
        = some ((read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P C))).getLsbD 0) := by
  obtain ⟨r3, m3, c3⟩ := run_cPre P rsp C acc sa hsp hd
  set sa3 := aMachine.runBlock sa ((cPre P C acc).map Prod.snd)
  rw [RInstrSemantics.Machine.runBlock_append]
  change (evalInstrA sa3 (cRst acc).2).regs = _ ∧ (evalInstrA sa3 (cRst acc).2).mem = _
    ∧ (evalInstrA sa3 (cRst acc).2).flags.cf = _
  obtain ⟨r4, m4⟩ := evalInstrA_loadMem_eq sa3 (SailX86Decoder.regName acc) "%rsp" cmovRedZone
  have hsp3 : sa3.regs "%rsp" = rsp := by rw [r3, ite_eq_right (Ne.symm hacc), hsp]
  have hm : (evalInstrA sa3 (cRst acc).2).mem
      = write64 sa.mem (redW rsp) (sa.regs (SailX86Decoder.regName acc)) := by
    show (evalInstrA sa3 (.loadMem _ "%rsp" cmovRedZone)).mem = _
    rw [m4, m3]
  refine ⟨funext fun r => ?_, hm, ?_⟩
  · show (evalInstrA sa3 (.loadMem _ "%rsp" cmovRedZone)).regs r = _
    rw [r4, hsp3, m3, r3]
    by_cases hr : r = SailX86Decoder.regName acc
    · subst hr
      rw [ite_eq_left rfl]
      exact read64_write64_same _ _ _
    · rw [ite_eq_right hr, ite_eq_right hr]
  · show (evalInstrA sa3 (.loadMem _ "%rsp" cmovRedZone)).flags.cf = _
    rw [evalInstrA_loadMem_flags, c3]

/-- A bit the address machine reads off a slot survives a register write. -/
theorem bitA_setReg_slot {frame : String → Option (BitVec 64)} {s : LstateA} {C D : String}
    {aC : BitVec 64} (hfC : frame C = some aC) {w : Nat} (v : BitVec w) :
    bitA frame { s with reg := (s.reg.setReg D v).nextPc } C = bitA frame s C := by
  simp [bitA, hfC]

/-- A general-purpose name is no slot name. -/
theorem ne_of_gp_slot {x y : String} (hx : gpOk x = true) (hy : isSpillOrQsave y = true) :
    x ≠ y := by
  rintro rfl
  simp [(gpFacts hx).notSlot] at hy

/-- The facts of the operands of a carry add with a slot carry-in. -/
theorem adcxc_facts {P : Params} {D A S C : String} (h : (SArm.adcxc D A S C).ok P = true) :
    isSpillOrQsave C = true ∧ kOk P C = true ∧ kOk P D = true ∧ kOk P A = true
      ∧ kOk P S = true ∧ (isSpillOrQsave D = true ∨ (A = D ∧ gpOk A = true) ∨ D ≠ S) := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hCs, hC⟩, hD⟩, hA⟩, hS⟩, hal⟩ := h
  exact ⟨hCs, hC, hD, hA, hS, by tauto⟩

/-- **The carry add with a slot carry-in into a register.** From `ACorrW`, the address-machine
    step of `ADCX:64 D, A, S, C` with `D` a register and `C` a frame slot is matched by the test
    of the frame word of `C` in the scratch, the restore of the scratch, the reload or copy of
    `A` into `D` and `adcx` from the slot or register `S`. -/
theorem sim_sadcxc_reg (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) (hDg : gpOk D = true) (sa : AState) (s : LstateA)
    (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcxc D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' A S C) := by
  obtain ⟨hCs, hC, hD, hA, hS, hal⟩ := adcxc_facts h
  have hDs : isSpillOrQsave D = false := (gpFacts hDg).notSlot
  have hfD : frameP P rsp D = none := frameP_gp hDg
  obtain ⟨oC, hoC, -, -⟩ : ∃ off, spillQsaveOff P.frame P.spillW C P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
    rcases kOk_cases hC with hg | h
    · simp [(gpFacts hg).notSlot] at hCs
    · exact h
  have hfC : frameP P rsp C = some (rsp + BitVec.ofInt 64 oC) := by simp [frameP, hoC]
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  set wc := valM P rsp sa C with hwc
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  have hC' := bitA_valM hc hC hCs
  rw [SArm.instr, fstepA_adcxSlotBit _ D A S C s zf (by simp [hfC]) hA' hS', hC'] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  set vc : BitVec 1 := wc.setWidth 1 with hvc
  set bit := wc.getLsbD 0 with hbit
  have hsp := hc.sp
  obtain ⟨hRg, -, -, -⟩ := scratchS_spec A S C
  set acc := gpNumU (scratchS A S C) with hacc
  have hRsp : SailX86Decoder.regName acc ≠ "%rsp" := (gpFacts hRg).physNe
  -- the run: the test and the restore, the copy of `A`, the add
  have hjs : (SArm.adcxc D A S C).js P
      = ((cPre P C acc).map Prod.snd ++ [(cRst acc).2])
        ++ ((sMv P D A (gpNumU D)).map Prod.snd ++ (sAd P S (gpNumU D)).map Prod.snd) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append, hacc]
  obtain ⟨r4, m4, c4⟩ := run_cTest P rsp C acc sa hsp hRsp (kOk_sep hC hCs rsp)
  set sa4 := aMachine.runBlock sa ((cPre P C acc).map Prod.snd ++ [(cRst acc).2]) with hsa4
  clear_value sa4
  have hcf4 : sa4.flags.cf.getD false = bit := by
    rw [c4]; simp [hbit, hwc, valM, hCs]
  have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, hsp]
  have hpD : SailX86Decoder.regName (gpNumU D) = phys D := rfl
  set sa5 := aMachine.runBlock sa4 ((sMv P D A (gpNumU D)).map Prod.snd) with hsa5
  obtain ⟨r5D, r5o, m5, f5⟩ : sa5.regs (phys D) = va ∧ (∀ r, r ≠ phys D → sa5.regs r = sa.regs r)
      ∧ sa5.mem = sa4.mem ∧ sa5.flags = sa4.flags := by
    by_cases hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU D = gpNumU D)
    · obtain ⟨hr, hm, hf⟩ := run_sMv P rsp D A (gpNumU D) sa4 hsp4 hlay
      refine ⟨by rw [hr, hpD, ite_eq_left rfl, valM_red hA r4 m4], fun r hr' => by
        rw [hr, hpD, ite_eq_right hr', r4], hm, hf⟩
    · simp only [not_or, Bool.not_eq_true, not_not] at hlay
      obtain ⟨hAs, rfl, -⟩ := hlay
      have he : sMv P A A (gpNumU A) = [] := by simp [sMv, hAs]
      have h0 : sa5 = sa4 := by rw [hsa5, he]; rfl
      rw [h0]
      exact ⟨by simp [hva, valM, hAs, r4], fun r _ => by rw [r4], rfl, rfl⟩
  clear_value sa5
  have hsp5 : sa5.regs "%rsp" = rsp := by
    rw [r5o _ (fun e => (gpFacts hDg).physNe e.symm), hsp]
  have hvb5 : valM P rsp sa5 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp only [valM, hSs, ite_true, m5, hvb]
      rw [m4]
      exact read64_write64_of_disjoint _ _ _ _ (kOk_sep hS hSs rsp)
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, ite_false, hvb]
      by_cases hSD : S = D
      · subst hSD
        rcases hal with hal | ⟨rfl, -⟩ | hal
        · simp [hDs] at hal
        · rw [r5D]; simp [hva, valM, (gpFacts hDg).notSlot]
        · exact absurd rfl hal
      · rw [r5o _ (fun e => hSD (phys_inj hSg hDg e))]
  obtain ⟨r6, m6, c6⟩ := run_sAd P rsp S (gpNumU D) sa5 hsp5
  rw [hpD, r5D, hvb5, f5, hcf4] at r6 c6
  have hvc0 : vc.getLsbD 0 = bit := by simp [hvc, hbit]
  have hword : (x86_ADCX va vb bit).2 = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [addCarryWord_eq, hvc0]; rfl
  rw [hjs, RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_append,
    ← hsa4, ← hsa5]
  refine ⟨hc.write hDg (VIR.JasminDialect.addCarryWord va vb vc) (fun r => ?_) (fun x hx => ?_)
    (fun r hr => ?_) ?_, rfl, fun hDA hDS => ⟨(waddcarry va vb bit).1, ?_,
      fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [r6, ← hword]
    split
    · rfl
    · rename_i hne; exact r5o _ hne
  · rw [m6, m5, m4, write64_of_not_inRange _ _ _ _ hx]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · left
    exact getW_setReg_nextPcN s.reg D D _ |>.trans (ite_eq_left rfl)
  · exact c6
  · rw [wordA_setReg (Ne.symm hDA)] at ha
    rw [wordA_setReg (Ne.symm hDS)] at hb
    rw [bitA_setReg_slot hfC] at hcc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans hC'
    simp only [Option.some.injEq] at e1 e2 e3
    subst e1 e2 e3
    rw [hvc0]

/-- A frame address read off a slot whose frame word is disjoint from that of `D`. -/
theorem frame_disj {P : Params} {rsp : BitVec 64} {D x : String} {offD : Int}
    (hsD : slotOff P D = offD) (hk : kOk P x = true)
    (hsep : isSpillOrQsave x = true → sepB (slotOff P D) (slotOff P x) = true) :
    ∀ ax, frameP P rsp x = some ax → Disjoint8 (rsp + BitVec.ofInt 64 offD) ax := by
  intro ax hax
  simp only [frameP_of_kOk hk, Option.map_eq_some_iff] at hax
  obtain ⟨off, hoff, rfl⟩ := hax
  have h := hsep (slot_facts hoff).1
  rw [hsD, show slotOff P x = off by simp [slotOff, hoff]] at h
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact disjoint8_add_ofInt rsp offD off h.1 h.2

/-- **The carry add with a slot carry-in into a slot.** From `ACorrW`, the address-machine step
    of `ADCX:64 D, A, S, C` with `D` and `C` frame slots is matched by the test of the frame word
    of `C` in the scratch, the reload or copy of `A` into the scratch, `adcx` from the slot or
    register `S`, the store into the slot of `D` and the restore of the scratch. -/
theorem sim_sadcxc_slot (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) (hDs : isSpillOrQsave D = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcxc D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S →
          (isSpillOrQsave A = true → sepB (slotOff P D) (slotOff P A) = true) →
          (isSpillOrQsave S = true → sepB (slotOff P D) (slotOff P S) = true) →
          sepB (slotOff P D) (slotOff P C) = true →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' A S C) := by
  obtain ⟨hCs, hC, hD, hA, hS, -⟩ := adcxc_facts h
  obtain ⟨offD, hoD, -, hsepD⟩ : ∃ off, spillQsaveOff P.frame P.spillW D P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
    rcases kOk_cases hD with hg | h
    · simp [(gpFacts hg).notSlot] at hDs
    · exact h
  have hsD : slotOff P D = offD := by simp [slotOff, hoD]
  set aD := rsp + BitVec.ofInt 64 offD with haD
  have hfD : frameP P rsp D = some aD := by simp [frameP, hoD, haD]
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  set wc := valM P rsp sa C with hwc
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  have hC' := bitA_valM hc hC hCs
  rw [SArm.instr, fstepA_adcxSlotBit _ D A S C s zf (by simp [hfD]) hA' hS', hC'] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  set vc : BitVec 1 := wc.setWidth 1 with hvc
  set bit := wc.getLsbD 0 with hbit
  have hvc0 : vc.getLsbD 0 = bit := by simp [hvc, hbit]
  have hsp := hc.sp
  obtain ⟨hRg, hRA, hRS, -⟩ := scratchS_spec A S C
  set acc := gpNumU (scratchS A S C) with hacc
  set R := SailX86Decoder.regName acc with hR
  have hRp : R = phys (scratchS A S C) := rfl
  have hRne : ∀ x, gpOk x = true → x ≠ scratchS A S C → phys x ≠ R := fun x hx hne e =>
    hne (phys_inj hx hRg (e.trans hRp))
  have hRsp : R ≠ "%rsp" := by rw [hRp]; exact (gpFacts hRg).physNe
  -- the run
  have hjs : (SArm.adcxc D A S C).js P
      = (cPre P C acc).map Prod.snd ++ ((sMv P D A acc).map Prod.snd
          ++ (sAd P S acc).map Prod.snd
          ++ [.storeMem "%rsp" (slotOff P D) (.reg R), .loadMem R "%rsp" cmovRedZone]) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append, cRst, hR, hacc]
  obtain ⟨r3, m3, c3⟩ := run_cPre P rsp C acc sa hsp (kOk_sep hC hCs rsp)
  set sa3 := aMachine.runBlock sa ((cPre P C acc).map Prod.snd) with hsa3
  clear_value sa3
  set old := sa.regs R with hold
  have hsp3 : sa3.regs "%rsp" = rsp := by rw [r3, ite_eq_right (Ne.symm hRsp), hsp]
  have hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ acc = gpNumU D) := by
    by_cases hAs : isSpillOrQsave A = true
    · exact Or.inl hAs
    · right; rintro ⟨rfl, -⟩; exact hAs hDs
  obtain ⟨r4, m4, f4⟩ := run_sMv P rsp D A acc sa3 hsp3 hlay
  set sa4 := aMachine.runBlock sa3 ((sMv P D A acc).map Prod.snd) with hsa4
  clear_value sa4
  have hva3 : valM P rsp sa3 A = va := by
    by_cases hAs : isSpillOrQsave A = true
    · simp only [valM, hAs, ite_true, hva, m3]
      exact read64_write64_of_disjoint _ _ _ _ (kOk_sep hA hAs rsp)
    · have hAg : gpOk A = true := by
        rcases kOk_cases hA with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hAs
      simp only [valM, hAs, Bool.false_eq_true, ite_false, hva]
      rw [r3, ite_eq_right (hRne A hAg (Ne.symm hRA))]
  have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, ite_eq_right (Ne.symm hRsp), hsp3]
  obtain ⟨r5, m5, c5⟩ := run_sAd P rsp S acc sa4 hsp4
  set sa5 := aMachine.runBlock sa4 ((sAd P S acc).map Prod.snd) with hsa5
  clear_value sa5
  have hvb4 : valM P rsp sa4 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp only [valM, hSs, ite_true, hvb, m4, m3]
      exact read64_write64_of_disjoint _ _ _ _ (kOk_sep hS hSs rsp)
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, ite_false, hvb]
      rw [r4, ite_eq_right (hRne S hSg (Ne.symm hRS)), r3, ite_eq_right (hRne S hSg (Ne.symm hRS))]
  have hcf4 : sa4.flags.cf.getD false = bit := by
    rw [f4, c3]; simp [hbit, hwc, valM, hCs]
  rw [show sa4.regs R = va by rw [r4, ite_eq_left rfl, hva3], hvb4, hcf4] at r5 c5
  set res := (x86_ADCX va vb bit).2 with hres
  set sa6 := evalInstrA sa5 (.storeMem "%rsp" (slotOff P D) (.reg R)) with hsa6
  obtain ⟨r6, m6⟩ := evalInstrA_storeMem_eq sa5 "%rsp" R (slotOff P D)
  rw [← hsa6] at r6 m6
  have hsp5 : sa5.regs "%rsp" = rsp := by rw [r5, ite_eq_right (Ne.symm hRsp), hsp4]
  rw [hsp5, hsD, r5, ite_eq_left rfl] at m6
  set sa7 := evalInstrA sa6 (.loadMem R "%rsp" cmovRedZone) with hsa7
  obtain ⟨r7, m7⟩ := evalInstrA_loadMem_eq sa6 R "%rsp" cmovRedZone
  rw [← hsa7] at r7 m7
  have hsp6 : sa6.regs "%rsp" = rsp := by rw [r6, hsp5]
  have hDisD : Disjoint8 aD (redW rsp) := by
    have := sepB_disj hsepD rsp
    exact ⟨this.2, this.1⟩
  have hrest : read64 sa6.mem (sa6.regs "%rsp" + BitVec.ofInt 64 cmovRedZone) = old := by
    rw [hsp6, m6, m5, m4, m3]
    show read64 (write64 (write64 sa.mem (redW rsp) old) aD res) (redW rsp) = old
    rw [read64_write64_of_disjoint _ _ _ _ hDisD, read64_write64_same]
  have hrun : aMachine.runBlock sa ((SArm.adcxc D A S C).js P) = sa7 := by
    rw [hjs, RInstrSemantics.Machine.runBlock_append, ← hsa3,
      RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_append, ← hsa4,
      ← hsa5]
    rfl
  have hword : res = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [hres, addCarryWord_eq, hvc0]; rfl
  rw [hrun]
  have hregs7 : sa7.regs = sa.regs := by
    funext r
    rw [r7, hrest, r6, r5]
    by_cases hr : r = R
    · subst hr; rw [ite_eq_left rfl]
    · rw [ite_eq_right hr, ite_eq_right hr, r4, ite_eq_right hr, r3, ite_eq_right hr]
  have hmem7 : sa7.mem = write64 (write64 sa.mem (redW rsp) old) aD res := by
    rw [m7, m6, m5, m4, m3]
  refine ⟨⟨fun r hr => ?_, by rw [hregs7]; exact hsp, fun x hx => ?_⟩, rfl,
    fun hDA hDS hsA hsS hsC => ⟨(waddcarry va vb bit).1, ?_, fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [hregs7]
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [LstateN.getW_nextPc]
    exact hc.regs r hr
  · show write64 s.mem aD _ x = _
    rw [hmem7, ← hword]
    refine agree_write64 (fun y hy => ?_) _ _ x hx
    rw [write64_of_not_inRange _ _ _ _ hy]
    exact hc.mem y hy
  · show sa7.flags.cf = _
    rw [hsa7, hsa6, evalInstrA_loadMem_flags, evalInstrA_storeMem_flags, c5]
    rfl
  · rw [wordA_write (frame_disj hsD hA hsA)] at ha
    rw [wordA_write (frame_disj hsD hS hsS)] at hb
    have hbC : bitA (frameP P rsp)
        { s with reg := s.reg.nextPc, mem := write64 s.mem aD (VIR.JasminDialect.addCarryWord va vb vc) } C
          = bitA (frameP P rsp) s C := by
      have hdC := frame_disj (rsp := rsp) hsD (x := C) hC (fun _ => hsC)
      unfold bitA
      split
      · rename_i ax hax
        simp only [Option.some.injEq]
        rw [read64_write64_of_disjoint _ _ _ _ (hdC ax hax)]
      · exact regBit_of_lvm (by simp [LstateN.nextPc])
    rw [hbC] at hcc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans hC'
    simp only [Option.some.injEq] at e1 e2 e3
    subst e1 e2 e3
    rw [hvc0]

/-- **The carry add with a slot carry-in.** From `ACorrW`, the address-machine step of
    `ADCX:64 D, A, S, C` with `C` a frame slot is matched by the machine instructions of its
    slot carry arm: the registers end related by `ACorrW`, the zero flag is kept, and, when `D`
    is none of `A`, `S` and its frame word is disjoint from those of `A`, `S` and `C`, the
    machine carry flag holds the carry-out of the add on the words of the result state. -/
theorem sim_sadcxc (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 = 64)
    (hwS : gpOk S = true → (s.reg.lvm S).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcxc D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → slotSepB P D A = true → slotSepB P D S = true →
          slotSepB P D C = true →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' A S C) := by
  obtain ⟨hCs, -, hD, -, -, -⟩ := adcxc_facts h
  by_cases hDs : isSpillOrQsave D = true
  · obtain ⟨h1, h2, h3⟩ := sim_sadcxc_slot P rsp D A S C h hDs sa s zf hc hwA hwS s' zf' hst
    refine ⟨h1, h2, fun hDA hDS hsa hss hsc => h3 hDA hDS (fun hAs => ?_) (fun hSs => ?_) ?_⟩
    · simpa [slotSepB, hDs, hAs] using hsa
    · simpa [slotSepB, hDs, hSs] using hss
    · simpa [slotSepB, hDs, hCs] using hsc
  · have hDg : gpOk D = true := by
      rcases kOk_cases hD with hg | ⟨off, hoff, -, -⟩
      · exact hg
      · exact absurd (slot_facts hoff).1 hDs
    obtain ⟨h1, h2, h3⟩ := sim_sadcxc_reg P rsp D A S C h hDg sa s zf hc hwA hwS s' zf' hst
    exact ⟨h1, h2, fun hDA hDS _ _ _ => h3 hDA hDS⟩

/-! ## 8b. The immediate store into a frame slot -/

/-- The immediate move `MOV:64 q, #v` into a frame-slot name `q`, as `(q, v)`. -/
def classifyI : LinstrR → Option (String × Nat)
  | .Lopn [.reg q] m [.imm v] =>
      if m = "MOV:64" ∧ isSpillOrQsave q = true then some (q, v) else none
  | _ => none

theorem classifyI_instr {i : LinstrR} {q : String} {v : Nat} (h : classifyI i = some (q, v)) :
    i = .Lopn [.reg q] "MOV:64" [.imm v] := by
  unfold classifyI at h
  split at h
  · split_ifs at h with hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hm.1]
  · cases h

/-- **The conditions of an immediate store into a frame slot**: `q` is a frame-slot name with a
    frame offset in `rel32` range, and `v` is a 64-bit value that sign-extends from 32 bits or
    whose slot word is disjoint from the red-zone word. -/
def iOk (P : Params) (q : String) (v : Nat) : Bool :=
  isSpillOrQsave q && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome
    && dispOk32 (slotOff P q) && decide (v < 2 ^ 64)
    && (ScalarEncoder.fitsImm32S v || sepB cmovRedZone (slotOff P q))

/-- The byte pieces of an immediate store into a frame slot: `movq $v, off(%rsp)` for a value
    that sign-extends from 32 bits; otherwise `%rax` saved to the red-zone word,
    `movabs $v, %rax`, `movq %rax, off(%rsp)` and `%rax` restored from the red-zone word. -/
def iPieces (P : Params) (q : String) (v : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if ScalarEncoder.fitsImm32S v then
    [(encMovImmRspMem 1 (slotOff P q) v, .storeMem "%rsp" (slotOff P q) (.imm v))]
  else
    [(encRspMem 1 0x89 (gpNumU "RAX") cmovRedZone,
        .storeMem "%rsp" cmovRedZone (.reg (phys "RAX"))),
      (ScalarEncoder.encMovImm64 (gpNumU "RAX") v, .mov (phys "RAX") (.imm v)),
      (encRspMem 1 0x89 (gpNumU "RAX") (slotOff P q),
        .storeMem "%rsp" (slotOff P q) (.reg (phys "RAX"))),
      (encRspMem 1 0x8b (gpNumU "RAX") cmovRedZone,
        .loadMem (phys "RAX") "%rsp" cmovRedZone)]

/-- `MOV:64 q, #v` into a frame slot `q` at offset `off`, with `v` sign-extending from
    32 bits, encodes to `movq $v, off(%rsp)`. -/
theorem encodeLopn_sti (F W : Nat) (q : String) (v : Nat) (qB : Nat) {off : Int}
    (hq : isSpillOrQsave q = true) (ho : spillQsaveOff F W q qB = some off)
    (hv : ScalarEncoder.fitsImm32S v = true) :
    encodeLopn F W (.Lopn [.reg q] "MOV:64" [.imm v]) qB = encMovImmRspMem 1 off v := by
  simp only [ScalarEncoder.fitsImm32S] at hv
  have h3 : LprogAsmPrinter.mnemWidth "MOV:64" = 64 := by decide +kernel
  simp only [encodeLopn,
    show (LprogAsmPrinter.isCarryOutBinding "MOV:64" || LprogAsmPrinter.isMulHiBinding "MOV:64")
      = false from by decide +kernel,
    show stripWidthTag "MOV:64" = "MOV" from by decide +kernel,
    show ("MOV" == "MULX") = false from by decide +kernel,
    show ("MOV" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "MOV" = none from by decide +kernel,
    LprogBytes.rexW, Bool.false_eq_true, ite_false]
  simp [hq, ho, hv, h3]

/-- `MOV:64 q, #v` into a frame slot `q` at offset `off`, with `v` outside the sign-extended
    `imm32` range, encodes to the save of `%rax` in the red-zone word, `movabs $v, %rax`, the
    store of `%rax` to the slot and the restore of `%rax`. -/
theorem encodeLopn_stiWide (F W : Nat) (q : String) (v : Nat) (qB : Nat) {off : Int}
    (hq : isSpillOrQsave q = true) (ho : spillQsaveOff F W q qB = some off)
    (hv : ScalarEncoder.fitsImm32S v = false) :
    encodeLopn F W (.Lopn [.reg q] "MOV:64" [.imm v]) qB
      = encRspMem 1 0x89 (gpNumU "RAX") (-128) ++ ScalarEncoder.encMovImm64 (gpNumU "RAX") v
        ++ encRspMem 1 0x89 (gpNumU "RAX") off ++ encRspMem 1 0x8b (gpNumU "RAX") (-128) := by
  simp only [ScalarEncoder.fitsImm32S] at hv
  have h3 : LprogAsmPrinter.mnemWidth "MOV:64" = 64 := by decide +kernel
  simp only [encodeLopn,
    show (LprogAsmPrinter.isCarryOutBinding "MOV:64" || LprogAsmPrinter.isMulHiBinding "MOV:64")
      = false from by decide +kernel,
    show stripWidthTag "MOV:64" = "MOV" from by decide +kernel,
    show ("MOV" == "MULX") = false from by decide +kernel,
    show ("MOV" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "MOV" = none from by decide +kernel,
    LprogBytes.rexW, Bool.false_eq_true, ite_false]
  simp [hq, ho, hv, h3]

/-- `movq $v, off(%rsp)` is the `[base + disp]` store-immediate encoder at base `%rsp`. -/
theorem encMovImmRspMem_eq (off : Int) (v : Nat) :
    encMovImmRspMem 1 off v = ScalarEncoder.encMemMovImm 4 off v := by
  simp only [encMovImmRspMem, ScalarEncoder.encMemMovImm, ScalarEncoder.encMemMov,
    ScalarEncoder.memTail, rexOpt_w1]
  split_ifs <;> simp_all [ScalarEncoder.rex]

/-- `movq $v, off(%rsp)` decodes to the store of `v` at `off` from `%rsp`. -/
theorem pieceDec_storeImmRsp (off : Int) (v : Nat) (hv : v < 2 ^ 64)
    (hf : ScalarEncoder.fitsImm32S v = true) (h : dispOk32 off = true) :
    PieceDec (encMovImmRspMem 1 off v, .storeMem "%rsp" off (.imm v)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_storeMemImm32 (canonAlloc ()) "%rsp" off v rest hv hf h
  have h4 : ScalarEncoder.gpNum (AsmPrinter.regOf (canonAlloc ()) "%rsp") = 4 := by decide
  have h5 : SailX86Decoder.regName 4 = "%rsp" := by decide
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, h4, h5, encMovImmRspMem_eq]
    using e

/-- `movabs $v, %r64` decodes to the 64-bit move of `v` into the register. -/
theorem pieceDec_movImm64 (D : String) (v : Nat) (hv : v < 2 ^ 64)
    (hf : ScalarEncoder.fitsImm32S v = false) :
    PieceDec (ScalarEncoder.encMovImm64 (gpNumU D) v, .mov (phys D) (.imm v)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have h31 : ¬ v < 2147483648 := by
    simp [ScalarEncoder.fitsImm32S] at hf
    omega
  have e := roundtrip_movImm (canonAlloc ()) (phys D) v rest hv
  simpa [ScalarEncoder.encodeJInstr, h31, renameJ, nameOf, operandOf, phys,
    regOf_canon (gpNumU_lt_16 D), gpNum_regName (gpNumU_lt_16 D)] using e

/-- **The bytes of an immediate store into a frame slot.** -/
theorem iBytes (P : Params) (q : String) (v : Nat) (h : iOk P q v = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg q] "MOV:64" [.imm v]) P.qsaveB
        = (iPieces P q v).flatMap Prod.fst
      ∧ ∀ p ∈ iPieces P q v, PieceDec p := by
  simp only [iOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hq, hs⟩, hd⟩, hv⟩, -⟩ := h
  obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 hs
  have hso : slotOff P q = off := by simp [slotOff, ho]
  have hl := gpNumU_lt_16 "RAX"
  cases hf : ScalarEncoder.fitsImm32S v with
  | true =>
    refine ⟨by simp [iPieces, hf, encodeLopn_sti _ _ _ _ _ hq ho hf, hso], ?_⟩
    intro p hp
    simp only [iPieces, hf, ite_true, List.mem_singleton] at hp
    subst hp
    exact pieceDec_storeImmRsp _ _ hv hf hd
  | false =>
    refine ⟨by simp [iPieces, hf, encodeLopn_stiWide _ _ _ _ _ hq ho hf, hso, cmovRedZone], ?_⟩
    intro p hp
    simp only [iPieces, hf, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact fun rest => decodeLinstr_rspStore _ cmovRedZone rest hl (by decide)
    · exact pieceDec_movImm64 "RAX" v hv hf
    · exact fun rest => decodeLinstr_rspStore _ _ rest hl hd
    · exact fun rest => decodeLinstr_rspLoad _ cmovRedZone rest hl (by decide)

/-- The machine store of an immediate keeps the registers and writes the 64-bit word of the
    immediate. -/
theorem evalInstrA_storeImm_eq (sa : AState) (B : String) (off : Int) (v : Nat) :
    (evalInstrA sa (.storeMem B off (.imm v))).regs = sa.regs
      ∧ (evalInstrA sa (.storeMem B off (.imm v))).mem
        = write64 sa.mem (sa.regs B + BitVec.ofInt 64 off) (BitVec.ofNat 64 v) := by
  refine ⟨?_, ?_⟩ <;>
    simp [evalInstrA, evalInstr, JState.store, AState.view, writeAddr, writeVal, JOperand.eval]

/-- The machine move of an immediate into a register writes its 64-bit word and keeps the
    memory. -/
theorem evalInstrA_movImm_eq (sa : AState) (R : String) (v : Nat) :
    (∀ r, (evalInstrA sa (.mov R (.imm v))).regs r
        = if r = R then BitVec.ofNat 64 v else sa.regs r)
      ∧ (evalInstrA sa (.mov R (.imm v))).mem = sa.mem := by
  refine ⟨fun r => ?_, evalInstrA_mem_of_noWriteB sa _ rfl⟩
  by_cases hr : r = R <;>
    simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_MOV, JOperand.eval]

/-- **The wide immediate store into a frame slot.** From `ACorrW`, the address-machine step of
    `MOV:64 q, #v`, which writes `v` to the slot word, is matched by the save of `%rax` in the
    red-zone word, `movabs $v, %rax`, the store of `%rax` to the slot and the restore of `%rax`,
    for a slot word disjoint from the red-zone word. -/
theorem sim_stiWide (P : Params) (rsp : BitVec 64) (q : String) (v : Nat) (off : Int)
    (hso : slotOff P q = off) (hf : ScalarEncoder.fitsImm32S v = false)
    (hsep : sepB cmovRedZone off = true) (sa : AState) (s : LstateA) (hc : ACorrW rsp sa s) :
    ACorrW rsp (aMachine.runBlock sa ((iPieces P q v).map Prod.snd))
      { s with reg := s.reg.nextPc,
               mem := write64 s.mem (rsp + BitVec.ofInt 64 off) (BitVec.ofNat 64 v) } := by
  set R := phys "RAX" with hR
  have hRsp : ("%rsp" = R) = False := by simp [hR, phys]; decide
  have hrun : aMachine.runBlock sa ((iPieces P q v).map Prod.snd)
      = evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
          (.storeMem "%rsp" cmovRedZone (.reg R))) (.mov R (.imm v)))
          (.storeMem "%rsp" off (.reg R))) (.loadMem R "%rsp" cmovRedZone) := by
    simp only [iPieces, hf, Bool.false_eq_true, ite_false, hso]; rfl
  rw [hrun]
  obtain ⟨r1, m1⟩ := evalInstrA_storeMem_eq sa "%rsp" R cmovRedZone
  set sa1 := evalInstrA sa (.storeMem "%rsp" cmovRedZone (.reg R))
  obtain ⟨r2, m2⟩ := evalInstrA_movImm_eq sa1 R v
  set sa2 := evalInstrA sa1 (.mov R (.imm v))
  obtain ⟨r3, m3⟩ := evalInstrA_storeMem_eq sa2 "%rsp" R off
  set sa3 := evalInstrA sa2 (.storeMem "%rsp" off (.reg R))
  obtain ⟨r4, m4⟩ := evalInstrA_loadMem_eq sa3 R "%rsp" cmovRedZone
  have hsp2 : sa2.regs "%rsp" = rsp := by
    rw [r2, ite_eq_right (by simp [hRsp]), r1, hc.sp]
  have hsp1 : sa1.regs "%rsp" = rsp := by rw [r1, hc.sp]
  have hdisj : Disjoint8 (rsp + BitVec.ofInt 64 cmovRedZone) (rsp + BitVec.ofInt 64 off) :=
    sepB_disj hsep rsp
  have hregs : ∀ r, (evalInstrA sa3 (.loadMem R "%rsp" cmovRedZone)).regs r = sa.regs r := by
    intro r
    rw [r4]
    by_cases hr : r = R
    · rw [ite_eq_left hr, r3, hsp2, m3, hsp2, read64_write64_of_disjoint _ _ _ _ hdisj.symm, m2,
        m1, hc.sp, read64_write64_same, hr]
    · rw [ite_eq_right hr, r3, r2, ite_eq_right hr, r1]
  refine ⟨fun r hr => ?_, by rw [hregs]; exact hc.sp, fun x hx => ?_⟩
  · rw [hregs]
    have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · show write64 s.mem _ _ x = _
    rw [m4, m3, hsp2, r2, ite_eq_left rfl, m2, m1, hc.sp]
    refine agree_write64 (fun y hy => ?_) _ _ x hx
    rw [hc.mem y hy, write64_of_not_inRange _ _ _ _ (by simpa [redW] using hy)]

/-- **The immediate store into a frame slot.** From `ACorrW`, the address-machine step of
    `MOV:64 q, #v` is matched by `movq $v, off(%rsp)`, or by the wide sequence of
    `sim_stiWide` for a value outside the sign-extended `imm32` range. -/
theorem sim_sti (P : Params) (rsp : BitVec 64) (q : String) (v : Nat) (h : iOk P q v = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg q] "MOV:64" [.imm v], .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((iPieces P q v).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [iOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨-, hs⟩, -⟩, -⟩, hfs⟩ := h
  obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 hs
  have hso : slotOff P q = off := by simp [slotOff, ho]
  have hfr : frameP P rsp q = some (rsp + BitVec.ofInt 64 off) := by simp [frameP, ho]
  rw [fstepA_slotImm _ hfr] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  cases hf : ScalarEncoder.fitsImm32S v with
  | false =>
    have hsep : sepB cmovRedZone off = true := by
      rw [← hso]; simpa [hf] using hfs
    exact ⟨sim_stiWide P rsp q v off hso hf hsep sa s hc, rfl⟩
  | true =>
  obtain ⟨hregs, hmem⟩ := evalInstrA_storeImm_eq sa "%rsp" off v
  have hrun : aMachine.runBlock sa ((iPieces P q v).map Prod.snd)
      = evalInstrA sa (.storeMem "%rsp" off (.imm v)) := by
    simp only [iPieces, hf, ite_true, hso]; rfl
  rw [hrun]
  refine ⟨⟨fun r hr => ?_, by rw [hregs]; exact hc.sp, fun x hx => ?_⟩, rfl⟩
  · rw [hregs]
    have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · show write64 s.mem _ _ x = _
    rw [hmem, hc.sp]
    exact agree_write64 hc.mem _ _ x hx

/-! ## 8c. The carry constant -/

/-- **The conditions of a carry constant** `MOV D, #n`: `D` is a general-purpose name and `n`
    is a bit. -/
def zOk (D : String) (n : Nat) : Bool := gpOk D && decide (n < 2)

/-- The byte piece of a carry constant: the 32-bit `mov $n, %r32`, which writes `n` to the
    64-bit register. -/
def zPieces (D : String) (n : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(encMovImmw 0 (gpNumU D) n, .mov (phys D) (.imm n))]

/-- The untagged `MOV D, #n` into a general-purpose name, with `n` below `2 ^ 31`, encodes to
    the 32-bit `mov $n, %r32`. -/
theorem encodeLopn_movImm32 (F W : Nat) (D : String) (n qB : Nat) (hD : gpOk D = true)
    (hn : n < 2 ^ 31) :
    encodeLopn F W (.Lopn [.reg D] "MOV" [.imm n]) qB = encMovImmw 0 (gpNumU D) n := by
  have fD := gpFacts hD
  simp only [encodeLopn,
    show (LprogAsmPrinter.isCarryOutBinding "MOV" || LprogAsmPrinter.isMulHiBinding "MOV")
      = false from by decide +kernel,
    show stripWidthTag "MOV" = "MOV" from by decide +kernel,
    show LprogAsmPrinter.mnemWidth "MOV" = 32 from by decide +kernel,
    show ("MOV" == "MULX") = false from by decide +kernel,
    show ("MOV" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "MOV" = none from by decide +kernel,
    LprogBytes.rexW, Bool.false_eq_true, ite_false, fD.notSlot, Bool.false_and]
  simp [encImmOp, fD.notSlot]
  intro h
  omega

/-- `mov $n, %r32` decodes to the 64-bit move of `n` into the register. -/
theorem pieceDec_movImm32 (D : String) (n : Nat) (hn : n < 2 ^ 32) :
    PieceDec (encMovImmw 0 (gpNumU D) n, .mov (phys D) (.imm n)) := by
  intro rest
  by_cases h8 : gpNumU D < 8
  · exact decodeLinstr_movImm32 _ _ rest h8 hn
  · exact decodeLinstr_movImm32_rex _ _ rest (by omega) (gpNumU_lt_16 D) hn

/-- **The bytes of a carry constant.** -/
theorem zBytes (P : Params) (D : String) (n : Nat) (h : zOk D n = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "MOV" [.imm n]) P.qsaveB
        = (zPieces D n).flatMap Prod.fst
      ∧ ∀ p ∈ zPieces D n, PieceDec p := by
  simp only [zOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hD, hn⟩ := h
  refine ⟨by simp [zPieces, encodeLopn_movImm32 _ _ _ _ _ hD (show n < 2 ^ 31 by omega)], ?_⟩
  intro p hp
  simp only [zPieces, List.mem_singleton] at hp
  subst hp
  exact pieceDec_movImm32 _ _ (by omega)

/-- **The carry constant.** From `ACorrW`, the address-machine step of `MOV D, #n` at the
    one-bit tag, which writes the bit `n` to `D`, is matched by `mov $n, %r32`, whose register
    holds the zero-extension of the bit. -/
theorem sim_bmov (P : Params) (rsp : BitVec 64) (D : String) (n : Nat) (h : zOk D n = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "MOV" [.imm n], .reg (some 1)) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((zPieces D n).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [zOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hD, hn⟩ := h
  rw [CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun.fstepA_bitMov _ D n s zf
    (frameP_gp hD)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hrun : aMachine.runBlock sa ((zPieces D n).map Prod.snd)
      = evalInstrA sa (.mov (phys D) (.imm n)) := rfl
  rw [hrun]
  refine ⟨hc.write hD (BitVec.ofNat 64 n) (fun r => rfl) (fun x hx => hc.mem x hx)
    (fun r hr => ?_) ?_, rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    refine ⟨BitVec.ofNat 1 n, ?_, ?_⟩
    · show (if D = D then _ else _) = _
      rw [ite_eq_left rfl]
    · interval_cases n <;> decide

/-- **The conditions of an untagged immediate move** `MOV D, #n`: `D` is a general-purpose
    name and `n` is below `2 ^ 31`, the range the 32-bit `mov $n, %r32` encodes. -/
def imm32Ok (D : String) (n : Nat) : Bool := gpOk D && decide (n < 2 ^ 31)

/-- The conditions of a carry constant give those of an untagged immediate move. -/
theorem imm32Ok_of_zOk {D : String} {n : Nat} (h : zOk D n = true) : imm32Ok D n = true := by
  simp only [zOk, imm32Ok, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, by omega⟩

/-- The bytes of an untagged immediate move are those of `zPieces`, and they decode. -/
theorem imm32Bytes (P : Params) (D : String) (n : Nat) (h : imm32Ok D n = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "MOV" [.imm n]) P.qsaveB
        = (zPieces D n).flatMap Prod.fst
      ∧ ∀ p ∈ zPieces D n, PieceDec p := by
  simp only [imm32Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hD, hn⟩ := h
  refine ⟨by simp [zPieces, encodeLopn_movImm32 _ _ _ _ _ hD hn], ?_⟩
  intro p hp
  simp only [zPieces, List.mem_singleton] at hp
  subst hp
  exact pieceDec_movImm32 _ _ (by omega)

/-- At the register tag without a descriptor, the untagged move `MOV D, #n` into a register
    `D` writes `n` at width `32` to `D`. -/
theorem fstepA_immMov32 (frame : String → Option (BitVec 64)) (D : String) (n : Nat)
    (s : LstateA) (zf : Bool) (hD : frame D = none) :
    fstepA frame (.Lopn [.reg D] "MOV" [.imm n], .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D (BitVec.ofNat 32 n)).nextPc }, zf) := by
  simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?,
    slotImm?, slotCmov?, regStepA, hD, VIR.JasminLsemMemFlagNestJoin.fstepF,
    VIR.JasminLsemMemFlagGuard.cmpArgs?, VIR.JasminLsemMemFlagGuard.movRegArgs?,
    VIR.JasminLsemMemFlagGuard.stepMemF, VIR.JasminLsemMem.lsemStepMem, lsemStepCast,
    castStruct?, movImmStruct?, VIR.JasminLsemMemFlagGuard.withALUFlags,
    VIR.JasminLsemMemFlagGuard.aluFlagOp?, lsemStepMC, mulhiStruct?, adcxStruct?,
    adcxhiStruct?, sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh,
    VIR.JasminLsemShift.sarStruct?, lsemStepN]
  rw [show widthFromTag "MOV" = 32 from by decide +kernel]

/-- **The untagged immediate move as a 32-bit constant.** From `ACorrW`, the
    address-machine step of `MOV D, #n` at the register tag without a descriptor, which
    writes `n` at width `32` to `D`, is matched by `mov $n, %r32`, whose register holds the
    zero-extension of the 32-bit cell (`NarrowCell`). -/
theorem sim_imov (P : Params) (rsp : BitVec 64) (D : String) (n : Nat) (h : imm32Ok D n = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "MOV" [.imm n], .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((zPieces D n).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [imm32Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hD, hn⟩ := h
  rw [fstepA_immMov32 _ D n s zf (frameP_gp hD)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hrun : aMachine.runBlock sa ((zPieces D n).map Prod.snd)
      = evalInstrA sa (.mov (phys D) (.imm n)) := rfl
  rw [hrun]
  refine ⟨hc.writeN hD (BitVec.ofNat 64 n) (fun r => rfl) (fun x hx => hc.mem x hx)
    (fun r hr => ?_) ?_, rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    right
    left
    refine ⟨BitVec.ofNat 32 n, ?_, ?_⟩
    · show (if D = D then _ else _) = _
      rw [ite_eq_left rfl]
    · apply BitVec.eq_of_toNat_eq
      simp
      omega

/-! ## 8d. The wide immediate -/

/-- The immediate move `MOV:64 D, #v` of a value outside the sign-extended `imm32` range, as
    `(D, v)`. -/
def classifyL : LinstrR → Option (String × Nat)
  | .Lopn [.reg d] m [.imm v] =>
      if m = "MOV:64" ∧ ScalarEncoder.fitsImm32S v = false then some (d, v) else none
  | _ => none

theorem classifyL_instr {i : LinstrR} {D : String} {v : Nat} (h : classifyL i = some (D, v)) :
    i = .Lopn [.reg D] "MOV:64" [.imm v] ∧ ScalarEncoder.fitsImm32S v = false := by
  unfold classifyL at h
  split at h
  · split_ifs at h with hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hm.1]
    exact ⟨rfl, hm.2⟩
  · cases h

/-- **The conditions of a wide immediate** `MOV:64 D, #v`: `D` is a general-purpose name and
    `v` is a 64-bit value outside the sign-extended `imm32` range. -/
def lOk (D : String) (v : Nat) : Bool :=
  gpOk D && decide (v < 2 ^ 64) && !ScalarEncoder.fitsImm32S v

/-- The byte piece of a wide immediate: `movabs $v, %r64`. -/
def lPieces (D : String) (v : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(ScalarEncoder.encMovImm64 (gpNumU D) v, .mov (phys D) (.imm v))]

/-- `MOV:64 D, #v` into a general-purpose name, with `v` outside the sign-extended `imm32`
    range, encodes to `movabs $v, %r64`. -/
theorem encodeLopn_movImm64 (F W : Nat) (D : String) (v qB : Nat) (hD : gpOk D = true)
    (hv : ScalarEncoder.fitsImm32S v = false) :
    encodeLopn F W (.Lopn [.reg D] "MOV:64" [.imm v]) qB
      = ScalarEncoder.encMovImm64 (gpNumU D) v := by
  have fD := gpFacts hD
  simp only [ScalarEncoder.fitsImm32S] at hv
  simp only [encodeLopn,
    show (LprogAsmPrinter.isCarryOutBinding "MOV:64" || LprogAsmPrinter.isMulHiBinding "MOV:64")
      = false from by decide +kernel,
    show stripWidthTag "MOV:64" = "MOV" from by decide +kernel,
    show LprogAsmPrinter.mnemWidth "MOV:64" = 64 from by decide +kernel,
    show ("MOV" == "MULX") = false from by decide +kernel,
    show ("MOV" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "MOV" = none from by decide +kernel,
    LprogBytes.rexW, Bool.false_eq_true, ite_false, ite_true, fD.notSlot, Bool.false_and]
  simp [encImmOp, fD.notSlot, hv]

/-- **The bytes of a wide immediate.** -/
theorem lBytes (P : Params) (D : String) (v : Nat) (h : lOk D v = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "MOV:64" [.imm v]) P.qsaveB
        = (lPieces D v).flatMap Prod.fst
      ∧ ∀ p ∈ lPieces D v, PieceDec p := by
  simp only [lOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hD, hv⟩, hf⟩ := h
  refine ⟨by simp [lPieces, encodeLopn_movImm64 _ _ _ _ _ hD hf], ?_⟩
  intro p hp
  simp only [lPieces, List.mem_singleton] at hp
  subst hp
  exact pieceDec_movImm64 _ _ hv hf

/-- The address-machine step of `MOV:64 D, #v` into a general-purpose name writes the 64-bit
    value of `v` to `D`. -/
theorem fstepA_movImm64 (P : Params) (rsp : BitVec 64) (D : String) (v : Nat)
    (hD : gpOk D = true) (s : LstateA) (zf : Bool) :
    fstepA (frameP P rsp) (.Lopn [.reg D] "MOV:64" [.imm v], .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D (BitVec.ofNat 64 v)).nextPc }, zf) := by
  rw [fstepA_of_reg (frameP P rsp) (i := (.Lopn [.reg D] "MOV:64" [.imm v], .reg none)) rfl
    (fun d x hs => by simp [slotMov?] at hs) (fun d x q hk => by simp [slotCmp?] at hk)
    (by simp [cellA?]) (by simp [slotCarry?]) (by simp [slotImm?, frameP_gp hD])
    (by simp [slotCmov?]) s zf (by simp [bitStepA])]
  have e := CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.fstepF_movII D v
    { reg := s.reg, cf := s.cf, of := s.of } zf
  rw [show CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.movII D v
    = (.Lopn [.reg D] "MOV:64" [.imm v], .reg none) from rfl] at e
  simp only [regStepA, e, Option.map_some]
  rfl

/-- **The wide immediate.** From `ACorrW`, the address-machine step of `MOV:64 D, #v` is
    matched by `movabs $v, %r64`. -/
theorem sim_lmov (P : Params) (rsp : BitVec 64) (D : String) (v : Nat) (h : lOk D v = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "MOV:64" [.imm v], .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((lPieces D v).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [lOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, -⟩, -⟩ := h
  rw [fstepA_movImm64 P rsp D v hD] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  have hrun : aMachine.runBlock sa ((lPieces D v).map Prod.snd)
      = evalInstrA sa (.mov (phys D) (.imm v)) := rfl
  rw [hrun]
  refine ⟨hc.write hD (BitVec.ofNat 64 v) (fun r => rfl) (fun x hx => hc.mem x hx)
    (fun r hr => ?_) (Or.inl ?_), rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_same _ _ _

/-! ## 8e. The register select -/

/-- The register select `CMOV:64 D, [C, A, B]` on register names, as `(D, C, A, B)`. -/
def classifyV : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg d] m [.reg c, .reg a, .reg b] =>
      if m = "CMOV:64" then some (d, c, a, b) else none
  | _ => none

theorem classifyV_instr {i : LinstrR} {D C A B : String}
    (h : classifyV i = some (D, C, A, B)) :
    i = .Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B] := by
  unfold classifyV at h
  split at h
  · split_ifs at h with hm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rw [hm]
  · cases h

/-- **The conditions of a register select** `CMOV:64 D, [C, A, B]`: general-purpose operands
    and a condition `C` that is none of `D`, `A`, `B`. -/
def vOk (D C A B : String) : Bool :=
  gpOk D && gpOk C && gpOk A && gpOk B && D != C && A != C && B != C

/-- The byte pieces of a register select: `test C, C` and `cmove B, D` when `D` is `A`;
    otherwise the copy of `B` into `D` unless they coincide, `test C, C` and `cmovne A, D`. -/
def vPieces (D C A B : String) : List (List (BitVec 8) × JInstr 64) :=
  if A = D then
    [(encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))),
      (enc0FRRw 1 0x44 (gpNumU D) (gpNumU B), .cmove (phys D) (.reg (phys B)))]
  else
    (if B = D then [] else
      [(encAluRRw 1 0x89 (gpNumU D) (gpNumU B), .mov (phys D) (.reg (phys B)))])
      ++ [(encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))),
        (enc0FRRw 1 0x45 (gpNumU D) (gpNumU A), .cmovne (phys D) (.reg (phys A)))]

/-- `test %c, %c` decodes to the self-test of the register. -/
theorem pieceDec_test (C : String) :
    PieceDec (encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_test (canonAlloc ()) (phys C) (phys C) rest
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, phys,
    regOf_canon (gpNumU_lt_16 C), gpNum_regName (gpNumU_lt_16 C),
    LprogJInstrBytesAgree.encAluRRw_one] using e

/-- `cmove %s, %d` decodes to the conditional move on the zero flag. -/
theorem pieceDec_cmove (D S : String) :
    PieceDec (enc0FRRw 1 0x44 (gpNumU D) (gpNumU S), .cmove (phys D) (.reg (phys S))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_cmove (canonAlloc ()) (phys D) (phys S) rest
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, phys,
    regOf_canon (gpNumU_lt_16 D), gpNum_regName (gpNumU_lt_16 D),
    regOf_canon (gpNumU_lt_16 S), gpNum_regName (gpNumU_lt_16 S),
    LprogJInstrBytesAgree.enc0FRRw_one] using e

/-- `cmovne %s, %d` decodes to the conditional move on the clear zero flag. -/
theorem pieceDec_cmovne (D S : String) :
    PieceDec (enc0FRRw 1 0x45 (gpNumU D) (gpNumU S), .cmovne (phys D) (.reg (phys S))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_cmovne (canonAlloc ()) (phys D) (phys S) rest
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, phys,
    regOf_canon (gpNumU_lt_16 D), gpNum_regName (gpNumU_lt_16 D),
    regOf_canon (gpNumU_lt_16 S), gpNum_regName (gpNumU_lt_16 S),
    LprogJInstrBytesAgree.enc0FRRw_one] using e

/-- **The bytes of a register select.** -/
theorem vBytes (P : Params) (D C A B : String) (h : vOk D C A B = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) P.qsaveB
        = (vPieces D C A B).flatMap Prod.fst
      ∧ ∀ p ∈ vPieces D C A B, PieceDec p := by
  simp only [vOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hC⟩, hA⟩, hB⟩, -⟩, -⟩, -⟩ := h
  have fD := gpFacts hD
  have fA := gpFacts hA
  have fB := gpFacts hB
  have fC := gpFacts hC
  refine ⟨?_, ?_⟩
  · rw [GatherFullBody.encodeLopn_cmov64_emits _ _ _ _ _ _ _
      (by simp [fD.isGp, fC.isGp, fA.isGp, fB.isGp])]
    simp only [encCmovSelect, GatherFullBody.gpNumU_beq_of_isGpName fD.isGp fA.isGp,
      GatherFullBody.gpNumU_beq_of_isGpName fD.isGp fB.isGp]
    by_cases hAD : A = D <;> by_cases hBD : B = D <;> simp [vPieces, hAD, hBD]
  · intro p hp
    simp only [vPieces] at hp
    split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact pieceDec_test C
      · exact pieceDec_cmove D B
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | rfl | rfl
      · split at hp
        · simp at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          exact pieceDec_movRR D B
      · exact pieceDec_test C
      · exact pieceDec_cmovne D A

/-- The address machine steps `CMOV:64 D, [C, A, B]` on names without a frame word by writing
    the select of the bit of `C` (`regBit`) between the 64-bit values of `A` and `B` to `D`. -/
theorem fstepA_cmovF (frame : String → Option (BitVec 64)) (D C A B : String)
    (hfD : frame D = none) (hfC : frame C = none) (hfA : frame A = none) (hfB : frame B = none)
    (s : LstateA) (zf : Bool)
    {va vb : BitVec 64} (ha : s.reg.getW A 64 = some va) (hb : s.reg.getW B 64 = some vb) :
    fstepA frame (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) s zf
      = (regBit s.reg C).map fun vc =>
          ({ s with reg := (s.reg.setReg D (VIR.JasminDialect.selectW vc va vb)).nextPc },
            zf) := by
  cases hc : s.reg.getW C 1 with
  | some vc =>
    rw [regBit_of_getW1 hc]
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?, lsemStepN,
      readReg_of_getW ha, hb, hc, withALUFlags, aluFlagOp?, cellA?,
      slotCarry?, slotImm?, slotCmov?, hfD, hfC, hfA, hfB, evalOperandN, operandName]
  | none =>
    have hw : wordA frame s A = some va := by simp [wordA, hfA, ha]
    have hw' : wordA frame s B = some vb := by simp [wordA, hfB, hb]
    have hbC : bitA frame s C = regBit s.reg C := bitA_of_none hfC s
    cases hr : regBit s.reg C <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?,
      VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?, lsemStepN,
      readReg_of_getW ha, hc, carryArgs?, wideArgs?, cellA?,
      slotCarry?, slotImm?, slotCmov?, hfD, hfC, hfA, hfB, operandName, bitStepA,
      hw, hw', hbC, hr]

/-- The address machine steps `CMOV:64 D, [C, A, B]` on registers by writing the select of the
    bit of `C` (`regBit`) between the 64-bit values of `A` and `B` to `D`. -/
theorem fstepA_cmov (P : Params) (rsp : BitVec 64) (D C A B : String) (hD : gpOk D = true)
    (hC : gpOk C = true) (hA : gpOk A = true) (hB : gpOk B = true) (s : LstateA) (zf : Bool)
    {va vb : BitVec 64} (ha : s.reg.getW A 64 = some va) (hb : s.reg.getW B 64 = some vb) :
    fstepA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) s zf
      = (regBit s.reg C).map fun vc =>
          ({ s with reg := (s.reg.setReg D (VIR.JasminDialect.selectW vc va vb)).nextPc },
            zf) :=
  fstepA_cmovF _ D C A B (frameP_gp hD) (frameP_gp hC) (frameP_gp hA) (frameP_gp hB) s zf ha hb

/-- **The machine run of a register select.** With the condition register other than the
    destination, the run writes to `D` the value of `B` on a zero condition and the value of `A`
    otherwise, keeps every other register, and keeps the memory. -/
theorem runBlock_vPieces (sa : AState) (D C A B : String) (hD : gpOk D = true)
    (hA : gpOk A = true) (hCD : phys C ≠ phys D) :
    (∀ r, (aMachine.runBlock sa ((vPieces D C A B).map Prod.snd)).regs r
      = if r = phys D then (if sa.regs (phys C) = 0 then sa.regs (phys B) else sa.regs (phys A))
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((vPieces D C A B).map Prod.snd)).mem = sa.mem := by
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by
    by_cases hAD : A = D <;> by_cases hBD : B = D <;> simp [vPieces, hAD, hBD, noWriteB])⟩
  by_cases hAD : A = D
  · subst hAD
    have hrun : aMachine.runBlock sa ((vPieces A C A B).map Prod.snd)
        = evalInstrA (evalInstrA sa (.test (phys C) (.reg (phys C))))
            (.cmove (phys A) (.reg (phys B))) := by
      simp [vPieces]; rfl
    rw [hrun]
    by_cases hr : r = phys A
    · subst hr
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.flagB, JState.writeB5,
        JState.get, JOperand.eval, x86_CMOVcc, x86_TEST, rflags_of_bwop, ZF_of_word,
        BitVec.toNat_eq]
    · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, hr]
  · by_cases hBD : B = D
    · subst hBD
      have hrun : aMachine.runBlock sa ((vPieces B C A B).map Prod.snd)
          = evalInstrA (evalInstrA sa (.test (phys C) (.reg (phys C))))
              (.cmovne (phys B) (.reg (phys A))) := by
        simp [vPieces, hAD]; rfl
      rw [hrun]
      by_cases hr : r = phys B
      · subst hr
        simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.flagB, JState.writeB5,
          JState.get, JOperand.eval, x86_CMOVcc, x86_TEST, rflags_of_bwop, ZF_of_word,
          BitVec.toNat_eq]
      · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, hr]
    · have hrun : aMachine.runBlock sa ((vPieces D C A B).map Prod.snd)
          = evalInstrA (evalInstrA (evalInstrA sa (.mov (phys D) (.reg (phys B))))
              (.test (phys C) (.reg (phys C)))) (.cmovne (phys D) (.reg (phys A))) := by
        simp [vPieces, hAD, hBD]; rfl
      rw [hrun]
      have hAD' : phys A ≠ phys D := fun e => hAD (phys_inj hA hD e)
      by_cases hr : r = phys D
      · subst hr
        simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.flagB, JState.writeB5,
          JState.get, JOperand.eval, x86_CMOVcc, x86_TEST, x86_MOV, rflags_of_bwop, ZF_of_word,
          BitVec.toNat_eq, hCD, hAD']
      · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, x86_MOV, hr]

/-- **The register select.** From `ACorrW`, with `A` and `B` at width `64`, the address-machine
    step of `CMOV:64 D, [C, A, B]`, which reads the condition `C` at width `1`, is matched by the
    `test` and conditional-move pieces: the condition register holds the zero-extension of the
    bit, so its zero test is the complement of the bit. -/
theorem sim_cmov (P : Params) (rsp : BitVec 64) (D C A B : String) (h : vOk D C A B = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwA : (s.reg.lvm A).1 = 64) (hwB : (s.reg.lvm B).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none)
      s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((vPieces D C A B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [vOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hC⟩, hA⟩, hB⟩, hDC⟩, -⟩, -⟩ := h
  have hgA := hc.wide hA hwA
  have hgB := hc.wide hB hwB
  rw [fstepA_cmov P rsp D C A B hD hC hA hB s zf hgA hgB] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  obtain ⟨hr, hm⟩ := runBlock_vPieces sa D C A B hD hA (fun e => hDC (phys_inj hD hC e.symm))
  refine ⟨hc.write hD (VIR.JasminDialect.selectW vc (sa.regs (phys A)) (sa.regs (phys B)))
    (fun r => ?_) (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_) (Or.inl ?_), rfl⟩
  · rw [hr, hmC]
    split
    · rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
        simp [VIR.JasminDialect.selectW]
    · rfl
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_same _ _ _

/-! ## 8f. The select with a true value in a frame slot -/

/-- **The conditions of a select with a slot true value** `CMOV:64 D, [C, A, B]`:
    general-purpose `D`, `C` and `B`, a frame slot `A` passing `kOk`, and a condition `C`
    that is neither `D` nor `B`. -/
def vtOk (P : Params) (D C A B : String) : Bool :=
  gpOk D && gpOk C && gpOk B && isSpillOrQsave A && kOk P A && D != C && B != C

/-- The byte pieces of a select with a slot true value: the copy of `B` into `D` unless they
    coincide, `test C, C` and `cmovne off(%rsp), D` from the frame slot of `A`. -/
def vtPieces (P : Params) (D C A B : String) : List (List (BitVec 8) × JInstr 64) :=
  (if B = D then [] else
    [(encAluRRw 1 0x89 (gpNumU D) (gpNumU B), .mov (phys D) (.reg (phys B)))])
    ++ [(encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))),
      (encCmovRspMem 1 0x45 (gpNumU D) (slotOff P A),
        .cmovccMem .ne (phys D) "%rsp" (slotOff P A))]

/-- `cmovne off(%rsp), %d` decodes to the conditional move from the frame word on the clear
    zero flag. -/
theorem pieceDec_cmovneRsp (D : String) (off : Int) (h : dispOk32 off = true) :
    PieceDec (encCmovRspMem 1 0x45 (gpNumU D) off, .cmovccMem .ne (phys D) "%rsp" off) := by
  intro rest
  have e := decodeLinstr_rspCmov .ne (gpNumU D) off rest (gpNumU_lt_16 D) h
  rw [show 0x40 + ScalarEncoder.condCode .ne = 0x45 from rfl] at e
  simpa [phys] using e

/-- **The bytes of a select with a slot true value.** -/
theorem vtBytes (P : Params) (D C A B : String) (h : vtOk P D C A B = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) P.qsaveB
        = (vtPieces P D C A B).flatMap Prod.fst
      ∧ ∀ p ∈ vtPieces P D C A B, PieceDec p := by
  simp only [vtOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hC⟩, hB⟩, hAs⟩, hAk⟩, -⟩, -⟩ := h
  have fD := gpFacts hD
  have fB := gpFacts hB
  have fC := gpFacts hC
  obtain ⟨off, hoff, hdisp, -⟩ := (kOk_cases hAk).resolve_left (by
    intro hg; simp [(gpFacts hg).notSlot] at hAs)
  have hso : slotOff P A = off := by simp [slotOff, hoff]
  have hAg : isGpName A = false := by
    cases hg : isGpName A
    · rfl
    · simp [(notSlotMem_of_isGpName hg).1] at hAs
  refine ⟨?_, ?_⟩
  · simp only [encodeLopn,
      show (LprogAsmPrinter.isCarryOutBinding "CMOV:64" || LprogAsmPrinter.isMulHiBinding "CMOV:64")
        = false from by decide +kernel,
      show stripWidthTag "CMOV:64" = "CMOV" from by decide +kernel,
      show LprogBytes.rexW (LprogAsmPrinter.mnemWidth "CMOV:64") = 1 from by decide +kernel,
      show ("CMOV" == "MULX") = false from by decide +kernel,
      show ("CMOV" == "MULXMEM") = false from by decide +kernel,
      show adxPrefix "CMOV" = none from by decide +kernel,
      show ("CMOV" == "CMOV") = true from by decide +kernel,
      fD.isGp, fC.isGp, fB.isGp, hAg, fD.off, fB.off, hoff, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [encCmovSelectSlotT, GatherFullBody.gpNumU_beq_of_isGpName fD.isGp fB.isGp]
    by_cases hBD : B = D <;> simp [vtPieces, hBD, hso]
  · intro p hp
    simp only [vtPieces, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl
    · split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact pieceDec_movRR D B
    · exact pieceDec_test C
    · rw [hso]
      exact pieceDec_cmovneRsp D off hdisp

/-- **The machine run of a select with a slot true value.** With the condition register other
    than the destination, the run writes to `D` the value of `B` on a zero condition and the
    frame word of `A` otherwise, keeps every other register, and keeps the memory. -/
theorem runBlock_vtPieces (P : Params) (sa : AState) (D C A B : String) (hD : gpOk D = true)
    (hCD : phys C ≠ phys D) :
    (∀ r, (aMachine.runBlock sa ((vtPieces P D C A B).map Prod.snd)).regs r
      = if r = phys D then (if sa.regs (phys C) = 0 then sa.regs (phys B)
          else read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 (slotOff P A)))
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((vtPieces P D C A B).map Prod.snd)).mem = sa.mem := by
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by
    by_cases hBD : B = D <;> simp [vtPieces, hBD, noWriteB])⟩
  have hsp : "%rsp" ≠ phys D := fun e => (gpFacts hD).physNe e.symm
  by_cases hBD : B = D
  · subst hBD
    have hrun : aMachine.runBlock sa ((vtPieces P B C A B).map Prod.snd)
        = evalInstrA (evalInstrA sa (.test (phys C) (.reg (phys C))))
            (.cmovccMem .ne (phys B) "%rsp" (slotOff P A)) := by
      simp [vtPieces]; rfl
    rw [hrun]
    by_cases hr : r = phys B
    · subst hr
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.condB, JState.flagB,
        JState.writeB5, JState.get, JState.load, JOperand.eval, x86_CMOVcc, x86_TEST,
        rflags_of_bwop, ZF_of_word, x86_eval_cond, writeAddr, BitVec.toNat_eq]
    · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, hr]
  · have hrun : aMachine.runBlock sa ((vtPieces P D C A B).map Prod.snd)
        = evalInstrA (evalInstrA (evalInstrA sa (.mov (phys D) (.reg (phys B))))
            (.test (phys C) (.reg (phys C)))) (.cmovccMem .ne (phys D) "%rsp" (slotOff P A)) := by
      simp [vtPieces, hBD]; rfl
    rw [hrun]
    by_cases hr : r = phys D
    · subst hr
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.condB, JState.flagB,
        JState.writeB5, JState.get, JState.load, JOperand.eval, x86_CMOVcc, x86_TEST, x86_MOV,
        rflags_of_bwop, ZF_of_word, x86_eval_cond, writeAddr, BitVec.toNat_eq, hCD, hsp]
    · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, x86_MOV, hr]

/-- **The select with a slot true value.** From `ACorrW`, with `B` at width `64`, the
    address-machine step of `CMOV:64 D, [C, A, B]`, which reads the true value at the frame
    word of `A`, is matched by the copy, `test` and `cmovne` pieces. -/
theorem sim_cmovSlot (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vtOk P D C A B = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwB : (s.reg.lvm B).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none)
      s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((vtPieces P D C A B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [vtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hC⟩, hB⟩, hAs⟩, hAk⟩, hDC⟩, -⟩ := h
  have hAg : gpOk A = false := by
    cases hg : gpOk A
    · rfl
    · simp [(gpFacts hg).notSlot] at hAs
  have hwa := wordA_valM hc hAk (fun hg => by rw [hAg] at hg; cases hg)
  have hwb := wordA_valM (P := P) hc (show kOk P B = true by simp [kOk, hB]) (fun _ => hwB)
  rw [fstepA_slotCmov (frameP P rsp) (frameP_gp hD) (by simp [kOk_frame hAk hAs rsp]) none s zf
    hwa hwb] at hst
  rw [bitA_of_none (frameP_gp hC)] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  obtain ⟨hr, hm⟩ := runBlock_vtPieces P sa D C A B hD (fun e => hDC (phys_inj hD hC e.symm))
  refine ⟨hc.write hD (VIR.JasminDialect.selectW vc (valM P rsp sa A) (valM P rsp sa B))
    (fun r => ?_) (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_) (Or.inl ?_), rfl⟩
  · rw [hr, hmC, hc.sp]
    simp only [valM, hAs, (gpFacts hB).notSlot, ite_true, Bool.false_eq_true, ite_false]
    split
    · rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
        simp_all [VIR.JasminDialect.selectW]
    · rfl
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_same _ _ _

/-! ## 8g. The select with a false value in a frame slot -/

/-- **The conditions of a select with a slot false value** `CMOV:64 D, [C, A, B]`:
    general-purpose `D` and `C`, a frame slot `B` passing `kOk` and other than `D`, a true value
    `A` passing `kOk`, and a condition `C` that is neither `D` nor `A`. A true value equal to `D`
    is printed as `vePieces`, any other as `vfPieces`. -/
def vfOk (P : Params) (D C A B : String) : Bool :=
  gpOk D && gpOk C && isSpillOrQsave B && kOk P B && kOk P A && D != C && A != C && B != D

/-- The conditional move of a select with a slot false value: `cmovne off(%rsp), D` from the
    frame slot of a slot true value `A`, and `cmovne A, D` from a register `A`. -/
def vfCm (P : Params) (D A : String) : List (BitVec 8) × JInstr 64 :=
  if isSpillOrQsave A then
    (encCmovRspMem 1 0x45 (gpNumU D) (slotOff P A), .cmovccMem .ne (phys D) "%rsp" (slotOff P A))
  else (enc0FRRw 1 0x45 (gpNumU D) (gpNumU A), .cmovne (phys D) (.reg (phys A)))

/-- The byte pieces of a select with a slot false value: the load of the frame word of `B` into
    `D`, `test C, C` and the conditional move `vfCm`. -/
def vfPieces (P : Params) (D C A B : String) : List (List (BitVec 8) × JInstr 64) :=
  [(encRspMem 1 0x8b (gpNumU D) (slotOff P B), .loadMem (phys D) "%rsp" (slotOff P B)),
    (encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))), vfCm P D A]

/-- A name passing `kOk` that is no frame slot is a general-purpose name. -/
theorem kOk_gp {P : Params} {x : String} (hk : kOk P x = true) (hs : isSpillOrQsave x = false) :
    gpOk x = true := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, -⟩
  · exact hg
  · simp [(slot_facts hoff).1] at hs

/-- **The bytes of a select with a slot false value**, the true value other than `D`. -/
theorem vfBytes (P : Params) (D C A B : String) (h : vfOk P D C A B = true) (hAD : A ≠ D) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B]) P.qsaveB
        = (vfPieces P D C A B).flatMap Prod.fst
      ∧ ∀ p ∈ vfPieces P D C A B, PieceDec p := by
  simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hC⟩, hBs⟩, hBk⟩, hAk⟩, -⟩, -⟩, -⟩ := h
  have fD := gpFacts hD
  have fC := gpFacts hC
  obtain ⟨offB, hoffB, hdispB, -⟩ := (kOk_cases hBk).resolve_left (by
    intro hg; simp [(gpFacts hg).notSlot] at hBs)
  have hsoB : slotOff P B = offB := by simp [slotOff, hoffB]
  have hBg : isGpName B = false := by
    cases hg : isGpName B
    · rfl
    · simp [(notSlotMem_of_isGpName hg).1] at hBs
  refine ⟨?_, ?_⟩
  · simp only [encodeLopn,
      show (LprogAsmPrinter.isCarryOutBinding "CMOV:64" || LprogAsmPrinter.isMulHiBinding "CMOV:64")
        = false from by decide +kernel,
      show stripWidthTag "CMOV:64" = "CMOV" from by decide +kernel,
      show LprogBytes.rexW (LprogAsmPrinter.mnemWidth "CMOV:64") = 1 from by decide +kernel,
      show ("CMOV" == "MULX") = false from by decide +kernel,
      show ("CMOV" == "MULXMEM") = false from by decide +kernel,
      show adxPrefix "CMOV" = none from by decide +kernel,
      show ("CMOV" == "CMOV") = true from by decide +kernel,
      fD.isGp, fC.isGp, hBg, fD.off, hoffB, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true]
    cases hAs : isSpillOrQsave A with
    | false =>
      have fA := gpFacts (kOk_gp hAk hAs)
      simp only [fA.isGp, ite_true, GatherFullBody.gpNumU_beq_of_isGpName fD.isGp fA.isGp,
        beq_iff_eq, hAD, ite_false]
      simp [vfPieces, vfCm, encCmovSelectSlotF, hAs, hsoB]
    | true =>
      obtain ⟨offA, hoffA, -, -⟩ := (kOk_cases hAk).resolve_left (by
        intro hg; simp [(gpFacts hg).notSlot] at hAs)
      have hAg : isGpName A = false := by
        cases hg : isGpName A
        · rfl
        · simp [(notSlotMem_of_isGpName hg).1] at hAs
      simp [hAg, hoffA, hoffB, vfPieces, vfCm, encCmovSelectSlotTF, hAs, slotOff]
  · intro p hp
    simp only [vfPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [hsoB]
      exact fun rest => decodeLinstr_rspLoad _ _ rest (gpNumU_lt_16 D) hdispB
    · exact pieceDec_test C
    · unfold vfCm
      split
      · rename_i hAs
        obtain ⟨offA, hoffA, hdispA, -⟩ := (kOk_cases hAk).resolve_left (by
          intro hg; simp [(gpFacts hg).notSlot] at hAs)
        rw [show slotOff P A = offA by simp [slotOff, hoffA]]
        exact pieceDec_cmovneRsp D offA hdispA
      · exact pieceDec_cmovne D A

/-- **The machine run of a select with a slot false value.** With the condition register and a
    register true value other than the destination, the run writes to `D` the frame word of `B`
    on a zero condition and the word of `A` otherwise, keeps every other register, and keeps the
    memory. -/
theorem runBlock_vfPieces (P : Params) (sa : AState) (D C A B : String) (hD : gpOk D = true)
    (hCD : phys C ≠ phys D) (hAD : isSpillOrQsave A = false → phys A ≠ phys D) :
    (∀ r, (aMachine.runBlock sa ((vfPieces P D C A B).map Prod.snd)).regs r
      = if r = phys D then (if sa.regs (phys C) = 0
            then read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 (slotOff P B))
          else if isSpillOrQsave A
            then read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 (slotOff P A))
          else sa.regs (phys A))
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((vfPieces P D C A B).map Prod.snd)).mem = sa.mem := by
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by
    cases hAs : isSpillOrQsave A <;> simp [vfPieces, vfCm, hAs, noWriteB])⟩
  have hsp : "%rsp" ≠ phys D := fun e => (gpFacts hD).physNe e.symm
  cases hAs : isSpillOrQsave A with
  | true =>
    have hrun : aMachine.runBlock sa ((vfPieces P D C A B).map Prod.snd)
        = evalInstrA (evalInstrA (evalInstrA sa (.loadMem (phys D) "%rsp" (slotOff P B)))
            (.test (phys C) (.reg (phys C)))) (.cmovccMem .ne (phys D) "%rsp" (slotOff P A)) := by
      simp [vfPieces, vfCm, hAs]; rfl
    rw [hrun]
    by_cases hr : r = phys D
    · subst hr
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.condB, JState.flagB,
        JState.writeB5, JState.get, JState.load, JOperand.eval, x86_CMOVcc, x86_TEST, x86_MOV,
        rflags_of_bwop, ZF_of_word, x86_eval_cond, writeAddr, BitVec.toNat_eq, hCD, hsp]
    · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, JState.load, hr]
  | false =>
    have hAD' := hAD hAs
    have hrun : aMachine.runBlock sa ((vfPieces P D C A B).map Prod.snd)
        = evalInstrA (evalInstrA (evalInstrA sa (.loadMem (phys D) "%rsp" (slotOff P B)))
            (.test (phys C) (.reg (phys C)))) (.cmovne (phys D) (.reg (phys A))) := by
      simp [vfPieces, vfCm, hAs]; rfl
    rw [hrun]
    by_cases hr : r = phys D
    · subst hr
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.flagB,
        JState.writeB5, JState.get, JState.load, JOperand.eval, x86_CMOVcc, x86_TEST, x86_MOV,
        rflags_of_bwop, ZF_of_word, writeAddr, BitVec.toNat_eq, hCD, hAD']
    · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, JState.load, hr]

/-- **The select with a slot false value.** From `ACorrW`, with a register true value at width
    `64`, the address-machine step of `CMOV:64 D, [C, A, B]`, which reads the false value at the
    frame word of `B`, is matched by the load, `test` and `cmovne` pieces. -/
theorem sim_cmovSlotF (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vfOk P D C A B = true) (hAD : A ≠ D) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s)
    (hwA : gpOk A = true → (s.reg.lvm A).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none)
      s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((vfPieces P D C A B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hC⟩, hBs⟩, hBk⟩, hAk⟩, hDC⟩, -⟩, -⟩ := h
  have hBg : gpOk B = false := by
    cases hg : gpOk B
    · rfl
    · simp [(gpFacts hg).notSlot] at hBs
  have hwa := wordA_valM hc hAk hwA
  have hwb := wordA_valM hc hBk (fun hg => by rw [hBg] at hg; cases hg)
  rw [fstepA_slotCmov (frameP P rsp) (frameP_gp hD) (by simp [kOk_frame hBk hBs rsp]) none s zf
    hwa hwb] at hst
  rw [bitA_of_none (frameP_gp hC)] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  obtain ⟨hr, hm⟩ := runBlock_vfPieces P sa D C A B hD (fun e => hDC (phys_inj hD hC e.symm))
    (fun hAs e => hAD (phys_inj (kOk_gp hAk hAs) hD e))
  refine ⟨hc.write hD (VIR.JasminDialect.selectW vc (valM P rsp sa A) (valM P rsp sa B))
    (fun r => ?_) (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_) (Or.inl ?_), rfl⟩
  · rw [hr, hmC, hc.sp]
    simp only [valM, hBs, ite_true]
    split
    · rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
        simp_all [VIR.JasminDialect.selectW]
    · rfl
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_same _ _ _

/-- The byte pieces of a select with a slot false value whose true value is the destination
    `D`: `test C, C` and `cmove off(%rsp), D` from the frame slot of `B`. -/
def vePieces (P : Params) (D C B : String) : List (List (BitVec 8) × JInstr 64) :=
  [(encAluRRw 1 0x85 (gpNumU C) (gpNumU C), .test (phys C) (.reg (phys C))),
    (encCmovRspMem 1 0x44 (gpNumU D) (slotOff P B), .cmovccMem .e (phys D) "%rsp" (slotOff P B))]

/-- `cmove off(%rsp), %d` decodes to the conditional move from the frame word on the set zero
    flag. -/
theorem pieceDec_cmoveRsp (D : String) (off : Int) (h : dispOk32 off = true) :
    PieceDec (encCmovRspMem 1 0x44 (gpNumU D) off, .cmovccMem .e (phys D) "%rsp" off) := by
  intro rest
  have e := decodeLinstr_rspCmov .e (gpNumU D) off rest (gpNumU_lt_16 D) h
  rw [show 0x40 + ScalarEncoder.condCode .e = 0x44 from rfl] at e
  simpa [phys] using e

/-- **The bytes of a select with a slot false value whose true value is the destination.** -/
theorem veBytes (P : Params) (D C B : String) (h : vfOk P D C D B = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] "CMOV:64" [.reg C, .reg D, .reg B]) P.qsaveB
        = (vePieces P D C B).flatMap Prod.fst
      ∧ ∀ p ∈ vePieces P D C B, PieceDec p := by
  simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hC⟩, hBs⟩, hBk⟩, -⟩, -⟩, -⟩, -⟩ := h
  have fD := gpFacts hD
  have fC := gpFacts hC
  obtain ⟨offB, hoffB, hdispB, -⟩ := (kOk_cases hBk).resolve_left (by
    intro hg; simp [(gpFacts hg).notSlot] at hBs)
  have hsoB : slotOff P B = offB := by simp [slotOff, hoffB]
  have hBg : isGpName B = false := by
    cases hg : isGpName B
    · rfl
    · simp [(notSlotMem_of_isGpName hg).1] at hBs
  refine ⟨?_, ?_⟩
  · simp only [encodeLopn,
      show (LprogAsmPrinter.isCarryOutBinding "CMOV:64" || LprogAsmPrinter.isMulHiBinding "CMOV:64")
        = false from by decide +kernel,
      show stripWidthTag "CMOV:64" = "CMOV" from by decide +kernel,
      show LprogBytes.rexW (LprogAsmPrinter.mnemWidth "CMOV:64") = 1 from by decide +kernel,
      show ("CMOV" == "MULX") = false from by decide +kernel,
      show ("CMOV" == "MULXMEM") = false from by decide +kernel,
      show adxPrefix "CMOV" = none from by decide +kernel,
      show ("CMOV" == "CMOV") = true from by decide +kernel,
      fD.isGp, fC.isGp, hBg, fD.off, hoffB, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, beq_self_eq_true]
    simp [vePieces, encCmovSelectSlotFE, hsoB]
  · intro p hp
    simp only [vePieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact pieceDec_test C
    · rw [hsoB]
      exact pieceDec_cmoveRsp D offB hdispB

/-- **The machine run of a select with a slot false value whose true value is the
    destination.** The run writes to `D` the frame word of `B` on a zero condition and keeps `D`
    otherwise, keeps every other register, and keeps the memory. -/
theorem runBlock_vePieces (P : Params) (sa : AState) (D C B : String) :
    (∀ r, (aMachine.runBlock sa ((vePieces P D C B).map Prod.snd)).regs r
      = if r = phys D then (if sa.regs (phys C) = 0
            then read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 (slotOff P B))
          else sa.regs (phys D))
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((vePieces P D C B).map Prod.snd)).mem = sa.mem := by
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by simp [vePieces, noWriteB])⟩
  have hrun : aMachine.runBlock sa ((vePieces P D C B).map Prod.snd)
      = evalInstrA (evalInstrA sa (.test (phys C) (.reg (phys C))))
          (.cmovccMem .e (phys D) "%rsp" (slotOff P B)) := by
    simp [vePieces]; rfl
  rw [hrun]
  by_cases hr : r = phys D
  · subst hr
    simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.condB, JState.flagB,
      JState.writeB5, JState.get, JState.load, JOperand.eval, x86_CMOVcc, x86_TEST,
      rflags_of_bwop, ZF_of_word, x86_eval_cond, writeAddr, BitVec.toNat_eq]
  · simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.writeB5, hr]

/-- **The select with a slot false value whose true value is the destination.** From `ACorrW`,
    with `D` at width `64`, the address-machine step of `CMOV:64 D, [C, D, B]`, which reads the
    false value at the frame word of `B`, is matched by the `test` and `cmove` pieces. -/
theorem sim_cmovSlotFE (P : Params) (rsp : BitVec 64) (D C B : String)
    (h : vfOk P D C D B = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwD : (s.reg.lvm D).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg D, .reg B], .reg none)
      s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((vePieces P D C B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hC⟩, hBs⟩, hBk⟩, hDk⟩, -⟩, -⟩, -⟩ := h
  have hBg : gpOk B = false := by
    cases hg : gpOk B
    · rfl
    · simp [(gpFacts hg).notSlot] at hBs
  have hwa := wordA_valM hc hDk (fun _ => hwD)
  have hwb := wordA_valM hc hBk (fun hg => by rw [hBg] at hg; cases hg)
  rw [fstepA_slotCmov (frameP P rsp) (frameP_gp hD) (by simp [kOk_frame hBk hBs rsp]) none s zf
    hwa hwb] at hst
  rw [bitA_of_none (frameP_gp hC)] at hst
  cases hgc : regBit s.reg C with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bitR hC hgc
  obtain ⟨hr, hm⟩ := runBlock_vePieces P sa D C B
  refine ⟨hc.write hD (VIR.JasminDialect.selectW vc (valM P rsp sa D) (valM P rsp sa B))
    (fun r => ?_) (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_) (Or.inl ?_), rfl⟩
  · rw [hr, hmC, hc.sp]
    simp only [valM, hBs, (gpFacts hD).notSlot, ite_true, Bool.false_eq_true, ite_false]
    split
    · rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
        simp_all [VIR.JasminDialect.selectW]
    · rfl
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · rw [LstateN.getW_nextPc]
    exact LstateN.getW_setReg_same _ _ _

/-! ## 8h. The register width casts -/

/-- **The cast on the address machine.** A cast `opn D, A` that `castStruct?` recognises,
    stepped at the descriptor tag `.reg (some w')`, is the typed cast step `lsemStepCast`: it
    writes the value of `A` zero-extended or truncated to width `w'` to `D`. -/
theorem fstepA_castW (frame : String → Option (BitVec 64)) (D A opn : String) (w' : Nat)
    (hcs : castStruct? (.Lopn [.reg D] opn [.reg A]) = some (D, A)) (s : LstateA) (zf : Bool) :
    fstepA frame (.Lopn [.reg D] opn [.reg A], .reg (some w')) s zf
      = (lsemStepCast (.Lopn [.reg D] opn [.reg A], some w') s.reg).map
          fun r => ({ s with reg := r }, zf) := by
  have hop : opn = "ZEROEXT" ∨ opn = "TRUNC" ∨ opn = "CASTW_32_32" ∨ opn = "CASTW_32_64"
      ∨ opn = "CASTW_64_32" ∨ opn = "CASTW_64_64" ∨ opn = "CASTW_64_16"
      ∨ opn = "CASTW_16_64" ∨ opn = "CASTW_16_16" ∨ opn = "CASTW_16_32"
      ∨ opn = "CASTW_32_16" := by
    simp only [castStruct?] at hcs
    split at hcs
    · assumption
    · cases hcs
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?,
    slotImm?, slotCmov?, regStepA, VIR.JasminLsemMemFlagNestJoin.fstepF,
    VIR.JasminLsemMemFlagGuard.cmpArgs?, VIR.JasminLsemMemFlagGuard.movRegArgs?,
    VIR.JasminLsemMemFlagGuard.stepMemF, VIR.JasminLsemMem.lsemStepMem, lsemStepCast,
    castStruct?, VIR.JasminLsemMemFlagGuard.withALUFlags,
    VIR.JasminLsemMemFlagGuard.aluFlagOp?, readReg]

/-- The typed cast step writes the value of the source at the descriptor width. -/
theorem lsemStepCast_castW (D A opn : String) (w' : Nat)
    (hcs : castStruct? (.Lopn [.reg D] opn [.reg A]) = some (D, A)) (s : LstateN) :
    lsemStepCast (.Lopn [.reg D] opn [.reg A], some w') s
      = some ((s.setReg D ((s.lvm A).2.zeroExtend w')).nextPc) := by
  simp [lsemStepCast, hcs, readReg]

/-- Bit `i` of `x86_MOVZX m v` is bit `i` of `v` below `m`. -/
theorem x86_MOVZX_getLsbD (m : Nat) (v : BitVec 64) (i : Nat) :
    (x86_MOVZX m v).getLsbD i = (decide (i < m) && v.getLsbD i) := by
  simp only [x86_MOVZX, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  by_cases h64 : i < 64
  · by_cases h : i < m <;> simp [h] <;> omega
  · simp [BitVec.getLsbD_of_ge v i (by omega)]

/-- Closes an equation between zero-extensions, truncations and `x86_MOVZX` words at the
    widths `1`, `8`, `16`, `32` and `64`, bit by bit. -/
local macro "movzx_cell" : tactic => `(tactic|
  (apply BitVec.eq_of_getLsbD_eq; intro i hi
   simp only [x86_MOVZX_getLsbD, BitVec.getLsbD_setWidth, BitVec.zeroExtend]
   all_goals
     have hge : ∀ {w : Nat} (x : BitVec w), w ≤ i → x.getLsbD i = false :=
       fun x h => BitVec.getLsbD_of_ge x i h
     by_cases hb : i = 0 <;> by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;>
       by_cases h32 : i < 32 <;> by_cases h64 : i < 64 <;>
       simp [hb, h8, h16, h32, h64] <;>
       first | omega | (exact hge _ (by omega)) | (exact (hge _ (by omega)).symm)))

/-- `movzx %s, %d` writes the low `m` bits of `s` zero-extended to `d` and keeps the
    memory. -/
theorem evalInstrA_movzx_eq (sa : AState) (d : String) (m : Nat) (src : String) :
    (∀ r, (evalInstrA sa (.movzx d m src)).regs r
        = if r = d then x86_MOVZX m (sa.regs src) else sa.regs r)
      ∧ (evalInstrA sa (.movzx d m src)).mem = sa.mem := by
  refine ⟨fun r => ?_, evalInstrA_mem_of_noWriteB sa _ rfl⟩
  by_cases hr : r = d <;>
    simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr]

/-- **The register width cast.** From `ACorrW`, the address-machine step of a cast
    `opn D, A` (`castStruct?`) at the descriptor width `w'` of `64`, `32` or `16`, which is
    `lsemStepCast` (`fstepA_castW`), is matched by `movzx %A, %D` of the low `m` bits, where
    `m` is the smaller of the width of `A` and `w'`, or `8` for a one-bit `A`: `movzwl` for a
    cast with a 16-bit side, `movl` (which the decoder reads as `movzx` of `32` bits) for a
    cast between 32 and 64 bits, `movzbl` for the zero-extension of a bit. The destination
    ends as a 64-bit, 32-bit or 16-bit cell of its register. -/
theorem sim_castW (P : Params) (rsp : BitVec 64) (D A opn : String) (w' m : Nat)
    (hD : gpOk D = true) (hA : gpOk A = true)
    (hcs : castStruct? (.Lopn [.reg D] opn [.reg A]) = some (D, A))
    (hw' : w' = 64 ∨ w' = 32 ∨ w' = 16)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hm : m = min (s.reg.lvm A).1 w' ∨ ((s.reg.lvm A).1 = 1 ∧ m = 8))
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] opn [.reg A], .reg (some w')) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa [.movzx (phys D) m (phys A)]) s' ∧ zf' = zf := by
  rw [fstepA_castW _ D A opn w' hcs, lsemStepCast_castW D A opn w' hcs] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨hregs, hmem⟩ := evalInstrA_movzx_eq sa (phys D) m (phys A)
  have hrun : aMachine.runBlock sa [.movzx (phys D) m (phys A)]
      = evalInstrA sa (.movzx (phys D) m (phys A)) := rfl
  rw [hrun]
  refine ⟨hc.writeN hD _ hregs (fun x hx => by rw [hmem]; exact hc.mem x hx)
    (fun r hr => ?_) ?_, rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · have hl : ((s.reg.setReg D ((s.reg.lvm A).2.zeroExtend w')).nextPc).lvm D
        = ⟨w', (s.reg.lvm A).2.zeroExtend w'⟩ := by
      simp [LstateN.nextPc, LstateN.setReg]
    show LstateN.getW _ D 64 = _ ∨ _
    rw [getW_eq_some_iff, hl]
    have hrA := hc.regs A hA
    rcases hcA : s.reg.lvm A with ⟨w0, va⟩
    rw [hcA] at hm hrA
    simp only at hm ⊢
    rcases hrA with hg | ⟨b, hb, hrb⟩ | ⟨b, hb, hrb⟩ | ⟨b, hb, hrb⟩
    on_goal 1 =>
      rw [lvm_of_getW hg] at hcA
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj hcA.symm
      obtain rfl := eq_of_heq hv
    on_goal 2 =>
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj hb
      obtain rfl := eq_of_heq hv
      rw [hrb]
    on_goal 3 =>
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj hb
      obtain rfl := eq_of_heq hv
      rw [hrb]
    on_goal 4 =>
      obtain ⟨rfl, hv⟩ := Sigma.mk.inj hb
      obtain rfl := eq_of_heq hv
      subst hrb
    all_goals
      rcases hw' with rfl | rfl | rfl <;> simp at hm <;> (try subst hm) <;>
        (try rcases hm with rfl | rfl)
    all_goals first
      | exact Or.inl (Sigma.ext rfl (heq_of_eq (by movzx_cell)))
      | exact Or.inr (Or.inr (Or.inl ⟨_, rfl, by movzx_cell⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨_, rfl, by movzx_cell⟩))

/-- The byte piece of a width-carrying cast of `A` into `D` that keeps the low `m` bits:
    the zero-extending move `encCastW`, decoded as `movzx`. -/
def castPieces (m : Nat) (D A : String) : List (List (BitVec 8) × JInstr 64) :=
  [(encCastW m (gpNumU D) (gpNumU A), .movzx (phys D) m (phys A))]

/-- A mnemonic `castMovBits` reads is a cast `castStruct?` recognises. -/
theorem castStruct?_of_castMovBits {o : String} {m : Nat} (h : castMovBits o = some m)
    (D A : String) : castStruct? (.Lopn [.reg D] o [.reg A]) = some (D, A) := by
  rcases castMovBits_cases h with ⟨-, rfl | rfl | rfl | rfl | rfl⟩ | ⟨-, rfl | rfl | rfl⟩ <;>
    simp [castStruct?]

/-- **The bytes of a width-carrying cast.** A cast `o D, A` between general-purpose names,
    with `castMovBits o = some m`, encodes to the piece `castPieces m D A`, which decodes
    to `movzx` of the low `m` bits. -/
theorem castBytes (P : Params) (o D A : String) (m : Nat) (hk : castMovBits o = some m)
    (hD : gpOk D = true) (hA : gpOk A = true) :
    encodeLopn P.frame P.spillW (.Lopn [.reg D] o [.reg A]) P.qsaveB
        = (castPieces m D A).flatMap Prod.fst
      ∧ ∀ p ∈ castPieces m D A, PieceDec p := by
  have hm : m = 16 ∨ m = 32 := by
    rcases castMovBits_cases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  refine ⟨by simp [castPieces,
    encodeLopn_castW _ _ _ _ _ _ _ hk (gpFacts hD).isGp (gpFacts hA).isGp], ?_⟩
  intro p hp rest
  simp only [castPieces, List.mem_singleton] at hp
  subst hp
  exact decodeLinstr_castW m _ _ rest hm (gpNumU_lt_16 D) (gpNumU_lt_16 A)

/-- **The decoded bytes of a width-carrying cast.** From `ACorrW`, the address-machine step
    of a cast `o D, A` at the descriptor width `w'` of `64`, `32` or `16`, with
    `castMovBits o = some m` and `m` the smaller of the width of `A` and `w'`, is matched by
    the decoded instructions of the piece `castPieces m D A` (`castBytes`). -/
theorem sim_castW_bytes (P : Params) (rsp : BitVec 64) (o D A : String) (w' m : Nat)
    (hk : castMovBits o = some m) (hD : gpOk D = true) (hA : gpOk A = true)
    (hw' : w' = 64 ∨ w' = 32 ∨ w' = 16)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hm : m = min (s.reg.lvm A).1 w') (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (.Lopn [.reg D] o [.reg A], .reg (some w')) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((castPieces m D A).map Prod.snd)) s' ∧ zf' = zf :=
  sim_castW P rsp D A o w' m hD hA (castStruct?_of_castMovBits hk D A) hw' sa s zf hc
    (Or.inl hm) s' zf' hst

/-! ## 9. The covered bodies with carry chains -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (aMachine_step_op)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)

/-- The carry arm of an instruction: `ADCX:64` and `ADCXHI:64` on three register sources. -/
def classifyC : LinstrR → Option CArm
  | .Lopn [.reg d] m [.reg a, .reg s, .reg c] =>
      if m = "ADCX:64" then some (.adcx d a s c)
      else if m = "ADCXHI:64" then some (.adcxhi d a s c) else none
  | _ => none

theorem classifyC_instr {i : LinstrR} {c : CArm} (h : classifyC i = some c) : c.instr = i := by
  unfold classifyC at h
  split at h
  · split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h; subst h1; rfl
    · obtain rfl := Option.some.inj h; subst h2; rfl
  · cases h

/-- The one-bit names an instruction reads: the carry-in of `ADCX:64` and `ADCXHI:64` and the
    condition of `CMOV:64`, none for any other instruction. -/
def carryIns : LinstrR → List String
  | .Lopn [.reg _] m [.reg x, .reg _, .reg c] =>
      if m = "ADCX:64" ∨ m = "ADCXHI:64" then [c] else if m = "CMOV:64" then [x] else []
  | _ => []

theorem carryIns_of_classifyC {i : LinstrR} (h : classifyC i = none) (hv : classifyV i = none) :
    carryIns i = [] := by
  unfold carryIns
  split
  · simp only [classifyC] at h
    simp only [classifyV] at hv
    split_ifs at h hv with h1 h2 h3
    simp [h1, h2, h3]
  · rfl

/-- The slot carry arm of an instruction: `ADCX:64` with a slot carry-in, `ADCX:64` with a
    frame slot among the destination and the word sources, `ADCXHI:64` with a frame slot among
    the word sources and the carry-in. -/
def classifyS : LinstrR → Option SArm
  | .Lopn [.reg d] m [.reg a, .reg s, .reg c] =>
      if m = "ADCX:64" ∧ isSpillOrQsave c = true then some (.adcxc d a s c)
      else if m = "ADCX:64" ∧ (isSpillOrQsave d || isSpillOrQsave a || isSpillOrQsave s) = true then
        some (.adcx d a s c)
      else if m = "ADCXHI:64" ∧ (isSpillOrQsave a || isSpillOrQsave s || isSpillOrQsave c) = true
      then
        some (.adcxhi d a s c)
      else none
  | _ => none

theorem classifyS_instr {i : LinstrR} {c : SArm} (h : classifyS i = some c) : c.instr = i := by
  unfold classifyS at h
  split at h
  · split_ifs at h with h0 h1 h2
    · obtain rfl := Option.some.inj h; obtain ⟨rfl, -⟩ := h0; rfl
    · obtain rfl := Option.some.inj h; obtain ⟨rfl, -⟩ := h1; rfl
    · obtain rfl := Option.some.inj h; obtain ⟨rfl, -⟩ := h2; rfl
  · cases h

/-- The width-carrying cast `o D, A` of an instruction: the destination `D`, the source `A`,
    the number of low source bits its zero-extending move keeps (`castMovBits`) and the
    destination width (`castTagW`). -/
def classifyK : LinstrR → Option (String × String × Nat × Nat)
  | .Lopn [.reg d] o [.reg a] =>
      match castMovBits o, castTagW o with
      | some m, some w => some (d, a, m, w)
      | _, _ => none
  | _ => none

theorem classifyK_spec {i : LinstrR} {d a : String} {m w : Nat}
    (h : classifyK i = some (d, a, m, w)) :
    ∃ o, i = .Lopn [.reg d] o [.reg a] ∧ castMovBits o = some m ∧ castTagW o = some w := by
  unfold classifyK at h
  split at h
  · rename_i d' o a'
    split at h
    · rename_i m' w' hm hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨o, rfl, hm, hw⟩
    · cases h
  · cases h

/-- The conditions of a cast arm: a general-purpose destination and source. -/
def castOk (d a : String) : Bool := gpOk d && gpOk a

/-- One step of the cast width analysis: a cast enters its destination at its destination
    width and keeps the entries of the other names; every other instruction empties the
    analysis. -/
def narrowStep (N : List (String × Nat)) (i : LinstrR) : List (String × Nat) :=
  match classifyK i with
  | some (d, _, _, w) => (d, w) :: N.filter (fun p => p.1 != d)
  | none => []

/-- **The cast width analysis** at instruction `k` of a body: the names written by the run of
    consecutive casts that ends directly before `k`, each with the destination width of the
    last cast that wrote it. -/
def narrowIn (body : Lcmd) (k : Nat) : List (String × Nat) :=
  (body.take k).foldl (fun N i => narrowStep N i.li_i) []

theorem narrowIn_zero (body : Lcmd) : narrowIn body 0 = [] := by
  simp [narrowIn]

theorem narrowIn_succ {body : Lcmd} {k : Nat} {bi : Linstr} (hb : body[k]? = some bi) :
    narrowIn body (k + 1) = narrowStep (narrowIn body k) bi.li_i := by
  unfold narrowIn
  rw [List.take_add_one, hb, Option.toList_some, List.foldl_append]
  rfl

/-- The source of the cast at instruction `k`, when the cast width analysis has an entry for
    it; no name otherwise. -/
def narrowSrc (body : Lcmd) (k : Nat) : List String :=
  match body[k]? with
  | some i =>
      match classifyK i.li_i with
      | some (_, a, _, _) => if ((narrowIn body k).lookup a).isSome then [a] else []
      | none => []
  | none => []

/-- At a cast, every name of the cast width analysis holds a value of the width of its
    entry. -/
def NarrowInv (body : Lcmd) (s : LstateA) : Prop :=
  ∀ i, body[s.reg.lpc]? = some i → (classifyK i.li_i).isSome = true →
    ∀ r w, (narrowIn body s.reg.lpc).lookup r = some w → (s.reg.lvm r).1 = w

/-- The cast at position `k` keeps as many low bits as the smaller of the width of its
    source, read off the cast width analysis and `64` without an entry, and its destination
    width. -/
def castPosB (body : Lcmd) (k : Nat) : Bool :=
  (body[k]?).all fun j =>
    match classifyK j.li_i with
    | some (_, a, m, w) => m == min (((narrowIn body k).lookup a).getD 64) w
    | none => true

/-- The cast width analyses `narrowIn body k` for `k ≤ body.length`, as an array indexed by
    `k`: the prefix folds of `narrowStep` over the body. -/
def narrowTable (body : Lcmd) : Array (List (String × Nat)) :=
  (body.scanl (fun N i => narrowStep N i.li_i) []).toArray

/-- Entry `k` of `narrowTable`, for `k ≤ body.length`, is the analysis `narrowIn body k`. -/
theorem narrowTable_getElem? (body : Lcmd) {k : Nat} (hk : k ≤ body.length) :
    (narrowTable body)[k]? = some (narrowIn body k) := by
  grind [narrowTable, narrowIn]

/-- `castPosB` over a body held as an array, with the cast width analyses read off the table
    `T`. -/
def castPosBA (body : Array Linstr) (T : Array (List (String × Nat))) (k : Nat) : Bool :=
  (body[k]?).all fun j =>
    match classifyK j.li_i with
    | some (_, a, m, w) => m == min ((((T[k]?).getD []).lookup a).getD 64) w
    | none => true

/-- `castPosBA` at the array of a body and its `narrowTable` is `castPosB`. -/
theorem castPosBA_toArray (body : Lcmd) :
    castPosBA body.toArray (narrowTable body) = castPosB body := by
  funext k
  by_cases hk : k < body.length
  · simp only [castPosBA, castPosB, List.getElem?_toArray, narrowTable_getElem? body hk.le,
      Option.getD_some]
  · have hn : body[k]? = none := List.getElem?_eq_none (by omega)
    simp only [castPosBA, castPosB, List.getElem?_toArray, hn, Option.all_none]

theorem lookup_filter_ne (N : List (String × Nat)) {d r : String} (hr : r ≠ d) :
    (N.filter (fun p => p.1 != d)).lookup r = N.lookup r := by
  induction N with
  | nil => rfl
  | cons p N ih =>
    obtain ⟨x, w⟩ := p
    by_cases hx : x = d
    · subst hx
      have hb : (r == x) = false := by simpa using hr
      simp [List.filter, List.lookup, hb, ih]
    · have hxd : (x != d) = true := by simpa using hx
      simp only [List.filter, hxd, List.lookup]
      rw [ih]

/-- **The cast width analysis is an invariant of the address machine.** -/
theorem narrowInv_step {frame : String → Option (BitVec 64)} {body : Lcmd} {s s' : LstateA}
    {zf zf' : Bool} (hI : NarrowInv body s) (hst : stepA frame body s zf = some (s', zf')) :
    NarrowInv body s' := by
  have hnext : ∀ bi, body[s.reg.lpc]? = some bi → classifyK bi.li_i = none →
      ∀ t : LstateA, t.reg.lpc = s.reg.lpc + 1 → NarrowInv body t := by
    intro bi hb hk t ht i _ _ r w hl
    rw [ht, narrowIn_succ hb, narrowStep, hk] at hl
    simp at hl
  unfold stepA at hst
  split at hst
  · rename_i ii ds o ss hb
    have hpc : s'.reg.lpc = s.reg.lpc + 1 := fstepA_lpc _ _ _ _ _ _ hst
    cases hk : classifyK (.Lopn ds o ss) with
    | none => exact hnext _ hb hk s' hpc
    | some q =>
      obtain ⟨d, a, m, w0⟩ := q
      obtain ⟨o', he, hm, hw⟩ := classifyK_spec hk
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [normA_castW hw, tagAt_castW _ _ hw,
        fstepA_castW _ d a o w0 (castStruct?_of_castMovBits hm d a),
        lsemStepCast_castW d a o w0 (castStruct?_of_castMovBits hm d a)] at hst
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, -⟩ := hst
      intro i _ _ r w hl
      have hpc' : ((s.reg.setReg d ((s.reg.lvm a).2.zeroExtend w0)).nextPc).lpc
          = s.reg.lpc + 1 := by simp [LstateN.setReg, LstateN.nextPc]
      change ((narrowIn body ((s.reg.setReg d ((s.reg.lvm a).2.zeroExtend w0)).nextPc).lpc).lookup r
        = some w) at hl
      rw [hpc', narrowIn_succ hb, narrowStep, hk] at hl
      show (((s.reg.setReg d ((s.reg.lvm a).2.zeroExtend w0)).nextPc).lvm r).1 = w
      by_cases hr : r = d
      · subst hr
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        subst hl
        simp [LstateN.setReg, LstateN.nextPc]
      · have hb' : (r == d) = false := by simpa using hr
        simp only [List.lookup, hb', lookup_filter_ne _ hr] at hl
        have := hI _ hb (by rw [hk]; rfl) r w hl
        simpa [LstateN.setReg, LstateN.nextPc, hr] using this
  · rename_i ii kd l hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
    exact hnext _ hb rfl _ rfl
  · rename_i ii cc l hb
    split at hst
    · rename_i pol hpol
      split_ifs at hst with hz
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hst
        obtain ⟨rfl, -⟩ := Prod.mk.inj he
        obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
        intro i hi hci
        change body[p]? = some i at hi
        rw [List.getElem?_eq_getElem hpl] at hi
        obtain rfl := Option.some.inj hi
        revert hlab hci
        rcases body[p] with ⟨ii', li'⟩
        cases li' <;> simp [isLabelB, classifyK]
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
        exact hnext _ hb rfl _ rfl
    · cases hst
  · cases hst

/-! ## 8i. The materialised comparison -/

/-- The relation of the materialised comparison: `.ne` for `SETNE`, `.eq` for `SETE`. -/
def eRel (n : Bool) : VIR.JasminDialect.JasminCmp := if n then .ne else .eq

/-- The mnemonic of the materialised comparison: `SETNE:64` or `SETE:64`. -/
def eMnem (n : Bool) : String := if n then "SETNE:64" else "SETE:64"

/-- The second opcode byte of `SET<cc>`: `95` for `SETNE`, `94` for `SETE`. -/
def eOpB (n : Bool) : Nat := if n then 0x95 else 0x94

/-- The materialised comparison `SETE:64 D, [A, B]` (`n = false`) or `SETNE:64 D, [A, B]`
    (`n = true`) over register names. -/
def eInstr (n : Bool) (D A B : String) : LinstrR := .Lopn [.reg D] (eMnem n) [.reg A, .reg B]

/-- The materialised comparison on register names, as `(n, D, A, B)` with `n` true for
    `SETNE:64`. -/
def classifyE : LinstrR → Option (Bool × String × String × String)
  | .Lopn [.reg d] m [.reg a, .reg b] =>
      if m = "SETE:64" then some (false, d, a, b)
      else if m = "SETNE:64" then some (true, d, a, b) else none
  | _ => none

theorem classifyE_instr {i : LinstrR} {n : Bool} {D A B : String}
    (h : classifyE i = some (n, D, A, B)) : i = eInstr n D A B := by
  unfold classifyE at h
  split at h
  · split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h1]; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h2]; rfl
  · cases h

/-- **The conditions of a materialised comparison** `SET<cc>:64 D, [A, B]`: general-purpose
    operands. -/
def eOk (D A B : String) : Bool := gpOk D && gpOk A && gpOk B

/-- The byte pieces of a materialised comparison: `cmp B, A`, `mov $0, D` and `set<cc> D8`. -/
def ePieces (n : Bool) (D A B : String) : List (List (BitVec 8) × JInstr 64) :=
  [(encAluRRw 1 0x39 (gpNumU A) (gpNumU B), .cmp (phys A) (.reg (phys B))),
    (encMovImmw 1 (gpNumU D) 0, .mov (phys D) (.imm 0)),
    (encSetccReg (eOpB n) (gpNumU D), .setcc (if n then .ne else .e) (phys D))]

/-- `mov $0, %r64` decodes to the move of `0` into the register. -/
theorem pieceDec_movZero (D : String) :
    PieceDec (encMovImmw 1 (gpNumU D) 0, .mov (phys D) (.imm 0)) :=
  fun rest => decodeLinstr_movImm _ _ rest (gpNumU_lt_16 D) (by norm_num) (by decide)

/-- `sete %r8` and `setne %r8` decode to `setcc` on the zero flag. -/
theorem pieceDec_setccE (n : Bool) (D : String) :
    PieceDec (encSetccReg (eOpB n) (gpNumU D), .setcc (if n then .ne else .e) (phys D)) := by
  intro rest
  have := decodeLinstr_setccReg (eOpB n) (gpNumU D) rest (by cases n <;> simp [eOpB])
    (gpNumU_lt_16 D)
  cases n <;> simpa [eOpB, phys] using this

/-- **The bytes of a materialised comparison.** -/
theorem eBytes (P : Params) (n : Bool) (D A B : String) (h : eOk D A B = true) :
    encodeLopn P.frame P.spillW (eInstr n D A B) P.qsaveB = (ePieces n D A B).flatMap Prod.fst
      ∧ ∀ p ∈ ePieces n D A B, PieceDec p := by
  simp only [eOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, hB⟩ := h
  have fD := gpFacts hD
  have fA := gpFacts hA
  have fB := gpFacts hB
  refine ⟨?_, ?_⟩
  · cases n <;>
      simp (config := { decide := true }) [eInstr, encodeLopn, eMnem, ePieces, eOpB, fD.isGp,
        fA.isGp, fB.isGp, tagShiftExt, aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix,
        LprogBytes.rexW, setccCmpOp, encSetccCmp]
  · intro p hp
    simp only [ePieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact pieceDec_cmpR A B
    · exact pieceDec_movZero D
    · exact pieceDec_setccE n D

/-- The address machine steps the materialised comparison on registers by writing the
    comparison bit `cmpBit` of the 64-bit values of `A` and `B` to `D` at width `1`, keeping
    the zero flag. -/
theorem fstepA_sete (P : Params) (rsp : BitVec 64) (n : Bool) (D A B : String)
    (s : LstateA) (zf : Bool)
    {va vb : BitVec 64} (ha : s.reg.getW A 64 = some va) (hb : s.reg.getW B 64 = some vb) :
    fstepA (frameP P rsp) (eInstr n D A B, .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D (VIR.JasminDialect.cmpBit (eRel n) va vb)).nextPc },
          zf) := by
  cases n <;>
    simp (config := { decide := true }) [eInstr, eMnem, eRel, fstepA, slotMov?, slotCmp?,
      regStepA, fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast,
      castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
      sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?,
      lsemStepN, readReg_of_getW ha, hb, withALUFlags, aluFlagOp?, cellA?, slotCarry?,
      slotImm?, slotCmov?, evalOperandN, applyOpnN, cmpOfName?,
      show stripWidthTag "SETE:64" = "SETE" from by decide +kernel,
      show stripWidthTag "SETNE:64" = "SETNE" from by decide +kernel]

/-- **The machine run of a materialised comparison.** The run writes to `D` the
    zero-extension of the comparison bit of the registers of `A` and `B`, keeps every other
    register, and keeps the memory. -/
theorem runBlock_ePieces (sa : AState) (n : Bool) (D A B : String) :
    (∀ r, (aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)).regs r
      = if r = phys D then
          (VIR.JasminDialect.cmpBit (eRel n) (sa.regs (phys A)) (sa.regs (phys B))).setWidth 64
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)).mem = sa.mem := by
  have hrun : aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)
      = evalInstrA (evalInstrA (evalInstrA sa (.cmp (phys A) (.reg (phys B))))
          (.mov (phys D) (.imm 0))) (.setcc (if n then .ne else .e) (phys D)) := rfl
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by simp [ePieces, noWriteB])⟩
  rw [hrun]
  by_cases hr : r = phys D
  · subst hr
    have hz := DecodedLsemStep.ZF_of_word_sub (sa.regs (phys A)) (sa.regs (phys B))
    cases n <;> by_cases he : sa.regs (phys A) = sa.regs (phys B) <;>
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.setRegMerge, JState.flagB,
        JState.writeB5, JState.get, JState.condB, JOperand.eval, x86_SETcc, x86_CMP, x86_MOV,
        VIR.JasminDialect.cmpBit, eRel, x86_SUB, x86_eval_cond, hz, he, wordExtendMerge,
        VIR.JasminDialect.JasminCmp.holds] <;> decide
  · cases n <;>
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.setRegMerge,
        JState.writeB5, x86_MOV, hr]

/-- **The materialised comparison.** From `ACorrW`, with `A` and `B` at width `64`, the
    address-machine step of `SET<cc>:64 D, [A, B]`, which writes the comparison bit to `D` at
    width `1`, is matched by `cmp`, `mov $0` and `set<cc>`: the register of `D` holds the
    zero-extension of the bit. -/
theorem sim_sete (P : Params) (rsp : BitVec 64) (n : Bool) (D A B : String)
    (h : eOk D A B = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwA : (s.reg.lvm A).1 = 64) (hwB : (s.reg.lvm B).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (eInstr n D A B, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [eOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, hB⟩ := h
  rw [fstepA_sete P rsp n D A B s zf (hc.wide hA hwA) (hc.wide hB hwB)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hr, hm⟩ := runBlock_ePieces sa n D A B
  refine ⟨hc.write hD _ hr (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_)
    (Or.inr ⟨_, ?_, rfl⟩), rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · simp [LstateN.nextPc, LstateN.setReg]

/-! ## 8j. The register-count shift -/

/-- The mnemonic of the register-count shift: `SHL:64` (`l = true`) or `SHR:64`. -/
def xMnem (l : Bool) : String := if l then "SHL:64" else "SHR:64"

/-- The register-count shift `SHL:64 D, [A, B]` (`l = true`) or `SHR:64 D, [A, B]`
    (`l = false`) of `A` by the count in `B`, over register names. -/
def xInstr (l : Bool) (D A B : String) : LinstrR := .Lopn [.reg D] (xMnem l) [.reg A, .reg B]

/-- The register-count shift on register names, as `(l, D, A, B)` with `l` true for
    `SHL:64`. -/
def classifyX : LinstrR → Option (Bool × String × String × String)
  | .Lopn [.reg d] m [.reg a, .reg b] =>
      if m = "SHL:64" then some (true, d, a, b)
      else if m = "SHR:64" then some (false, d, a, b) else none
  | _ => none

theorem classifyX_instr {i : LinstrR} {l : Bool} {D A B : String}
    (h : classifyX i = some (l, D, A, B)) : i = xInstr l D A B := by
  unfold classifyX at h
  split at h
  · split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h1]; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h2]; rfl
  · cases h

/-- **The conditions of a register-count shift** `SH<d>:64 D, [A, B]`: general-purpose
    operands. -/
def xOk (D A B : String) : Bool := gpOk D && gpOk A && gpOk B

/-- The word the register-count shift writes: `a` shifted left (`l = true`) or logically
    right by the count `b` masked to `0 … 63`. -/
def xVal (l : Bool) (a b : BitVec 64) : BitVec 64 :=
  if l then a <<< VIR.shiftMask 64 b.toNat else a >>> VIR.shiftMask 64 b.toNat

/-- The BMI2 shift `shlx` (`l = true`) or `shrx` of `A` by `B` into `D`. -/
def xJ (l : Bool) (D A B : String) : JInstr 64 :=
  (if l then JInstr.shlx else JInstr.shrx) (phys D) (phys A) (phys B)

/-- The byte piece of a register-count shift: `shlx`/`shrx %B, %A, %D` (`encShiftX`). -/
def xPieces (l : Bool) (D A B : String) : List (List (BitVec 8) × JInstr 64) :=
  [(ScalarEncoder.encShiftX (if l then 4 else 5) (gpNumU D) (gpNumU A) (gpNumU B), xJ l D A B)]

/-- `shlx` and `shrx` decode to the BMI2 shifts of the register numbers. -/
theorem pieceDec_shiftX (l : Bool) (D A B : String) :
    PieceDec (ScalarEncoder.encShiftX (if l then 4 else 5) (gpNumU D) (gpNumU A) (gpNumU B),
      xJ l D A B) := by
  intro rest
  have := decodeLinstr_shiftX (if l then 4 else 5) (gpNumU D) (gpNumU A) (gpNumU B) rest
    (by cases l <;> simp) (gpNumU_lt_16 D) (gpNumU_lt_16 A) (gpNumU_lt_16 B)
  cases l <;> simpa [xJ, phys] using this

/-- **The bytes of a register-count shift.** -/
theorem xBytes (P : Params) (l : Bool) (D A B : String) (h : xOk D A B = true) :
    encodeLopn P.frame P.spillW (xInstr l D A B) P.qsaveB = (xPieces l D A B).flatMap Prod.fst
      ∧ ∀ p ∈ xPieces l D A B, PieceDec p := by
  simp only [xOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, hB⟩ := h
  have fD := gpFacts hD
  have fA := gpFacts hA
  have fB := gpFacts hB
  refine ⟨?_, ?_⟩
  · cases l <;>
      simp (config := { decide := true }) [xInstr, encodeLopn, xMnem, xPieces, fD.isGp,
        fA.isGp, fB.isGp, tagShiftExt, aluOpcode, twoByteOpcode, stripWidthTag, adxPrefix]
  · intro p hp
    simp only [xPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact pieceDec_shiftX l D A B

/-- The address machine steps the register-count shift on registers by writing the shift
    `xVal` of the 64-bit values of `A` and `B` to `D`, keeping the zero flag. -/
theorem fstepA_shrx (P : Params) (rsp : BitVec 64) (l : Bool) (D A B : String)
    (s : LstateA) (zf : Bool)
    {va vb : BitVec 64} (ha : s.reg.getW A 64 = some va) (hb : s.reg.getW B 64 = some vb) :
    fstepA (frameP P rsp) (xInstr l D A B, .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D (xVal l va vb)).nextPc }, zf) := by
  cases l <;>
    simp (config := { decide := true }) [xInstr, xMnem, xVal, fstepA, slotMov?, slotCmp?,
      regStepA, fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast,
      castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
      sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?,
      lsemStepN, readReg_of_getW ha, hb, withALUFlags, aluFlagOp?, cellA?, slotCarry?,
      slotImm?, slotCmov?, evalOperandN, applyOpnN,
      show stripWidthTag "SHL:64" = "SHL" from by decide +kernel,
      show stripWidthTag "SHR:64" = "SHR" from by decide +kernel]

/-- **The machine run of a register-count shift.** The run writes to `D` the shift `xVal`
    of the registers of `A` and `B`, keeps every other register, and keeps the memory. -/
theorem runBlock_xPieces (sa : AState) (l : Bool) (D A B : String) :
    (∀ r, (aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)).regs r
      = if r = phys D then xVal l (sa.regs (phys A)) (sa.regs (phys B)) else sa.regs r)
      ∧ (aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)).mem = sa.mem := by
  have hrun : aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)
      = evalInstrA sa (xJ l D A B) := rfl
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by cases l <;> simp [xPieces, xJ,
    noWriteB])⟩
  rw [hrun]
  by_cases hr : r = phys D
  · subst hr
    cases l <;>
      simp [evalInstrA, evalInstr, xJ, xVal, AState.view, JState.setReg, JState.get,
        x86_SHLX, x86_SHRX, wshl, wshr, shiftCount, VIR.shiftMask,
        Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 64))]
  · cases l <;>
      simp [evalInstrA, evalInstr, xJ, AState.view, JState.setReg, hr]

/-- **The register-count shift.** From `ACorrW`, with `A` and `B` at width `64`, the
    address-machine step of `SH<d>:64 D, [A, B]` is matched by `shlx`/`shrx`: the register of
    `D` holds the shifted word. -/
theorem sim_shrx (P : Params) (rsp : BitVec 64) (l : Bool) (D A B : String)
    (h : xOk D A B = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwA : (s.reg.lvm A).1 = 64) (hwB : (s.reg.lvm B).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (xInstr l D A B, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [xOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, hB⟩ := h
  have ha := hc.wide hA hwA
  have hb := hc.wide hB hwB
  rw [fstepA_shrx P rsp l D A B s zf ha hb] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hr, hm⟩ := runBlock_xPieces sa l D A B
  refine ⟨hc.write hD _ hr (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_)
    (Or.inl ?_), rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · exact (getW_setReg_nextPcN _ D D _).trans (ite_eq_left rfl)

/-! ## 8k. The materialised comparison with an immediate -/

/-- The materialised comparison `SETE:64 D, [A, $v]` (`n = false`) or `SETNE:64 D, [A, $v]`
    (`n = true`) of a register name with an immediate. -/
def eiInstr (n : Bool) (D A : String) (v : Nat) : LinstrR :=
  .Lopn [.reg D] (eMnem n) [.reg A, .imm v]

/-- The materialised comparison with an immediate, as `(n, D, A, v)` with `n` true for
    `SETNE:64`. -/
def classifyEI : LinstrR → Option (Bool × String × String × Nat)
  | .Lopn [.reg d] m [.reg a, .imm v] =>
      if m = "SETE:64" then some (false, d, a, v)
      else if m = "SETNE:64" then some (true, d, a, v) else none
  | _ => none

theorem classifyEI_instr {i : LinstrR} {n : Bool} {D A : String} {v : Nat}
    (h : classifyEI i = some (n, D, A, v)) : i = eiInstr n D A v := by
  unfold classifyEI at h
  split at h
  · split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h1]; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [h2]; rfl
  · cases h

/-- **The conditions of a materialised comparison with an immediate**
    `SET<cc>:64 D, [A, $v]`: general-purpose operands and an immediate below `2^31`, the
    immediates the printer renders as a sign-extended `imm8` or `imm32`. -/
def eiOk (D A : String) (v : Nat) : Bool := gpOk D && gpOk A && decide (v < 2 ^ 31)

/-- The bytes of `cmp $v, %A`: the `imm8` form when `v` fits a sign-extended byte, the
    `imm32` form otherwise. -/
def eiCmp (A : String) (v : Nat) : List (BitVec 8) :=
  if fitsImm8S 1 v then encAluImm8 1 7 (gpNumU A) v else encAluImmw 1 7 (gpNumU A) v

/-- The byte pieces of a materialised comparison with an immediate, the three lines of
    `encSetccCmpImm`: `cmp $v, A`, `mov $0, D` and `set<cc> D8`. -/
def eiPieces (n : Bool) (D A : String) (v : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(eiCmp A v, .cmp (phys A) (.imm v)),
    (encMovImmw 1 (gpNumU D) 0, .mov (phys D) (.imm 0)),
    (encSetccReg (eOpB n) (gpNumU D), .setcc (if n then .ne else .e) (phys D))]

/-- The `imm32` compare `CMP $v, %d` (`REX.W 81 /7 id`) with `v < 2^31` decodes to the
    compare of `d` against the immediate. -/
theorem decodeLinstr_cmpImm31 (d v : Nat) (rest : List (BitVec 8)) (hd : d < 16)
    (hv : v < 2 ^ 31) :
    decodeLinstr (encAluImmw 1 7 d v ++ rest)
      = some (.op (.cmp (SailX86Decoder.regName d) (.imm v)), rest) := by
  have hnone : decodeRex (BitVec.ofNat 8 (ScalarEncoder.rex 1 0 0 (ScalarEncoder.bit d 3)))
      (BitVec.ofNat 8 0x81 :: BitVec.ofNat 8 (ScalarEncoder.modRMReg 7 d)
        :: (ScalarEncoder.imm32LE v ++ rest)) = none := by
    simp [decodeRex, modField_modRMReg, regField_modRMReg, aluImmMnemonic,
      ScalarEncoder.imm32LE]
  apply decodeLinstr_of_decodeJ1_6
  simp only [encAluImmw, rexOpt_w1, List.cons_append, List.nil_append]
  rw [decodeJ1_6_of_none _ (by
    rw [decodeJ1_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _)]; exact hnone)]
  have himm := imm32S_imm32LE v (by omega) (by simp; omega)
  unfold imm32S at himm
  simp only [ScalarEncoder.imm32LE, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    decodeShift1, decodeCmp,
    isRex_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexW_rex _ _ _ (Nat.zero_le 1) (Nat.zero_le 1) (bit_le_one _ _),
    rexB_rex _ _ _ (bit_le_one _ _), BitVec.toNat_ofNat, modField_modRMReg,
    regField_modRMReg, rmField_modRMReg, bitsplit _ hd, true_and, ite_true] at himm ⊢
  simp [himm]

/-- `cmp $v, %r64` with `v < 2^31` decodes to the compare against the immediate. -/
theorem pieceDec_cmpImm (A : String) (v : Nat) (hv : v < 2 ^ 31) :
    PieceDec (eiCmp A v, .cmp (phys A) (.imm v)) := by
  intro rest
  unfold eiCmp
  split
  · exact decodeLinstr_aluImm8 7 JInstr.cmp _ _ rest (by decide) (gpNumU_lt_16 A)
      (by assumption) rfl
  · simpa [phys] using decodeLinstr_cmpImm31 _ _ rest (gpNumU_lt_16 A) hv

/-- **The bytes of a materialised comparison with an immediate.** -/
theorem eiBytes (P : Params) (n : Bool) (D A : String) (v : Nat) (h : eiOk D A v = true) :
    encodeLopn P.frame P.spillW (eiInstr n D A v) P.qsaveB
        = (eiPieces n D A v).flatMap Prod.fst
      ∧ ∀ p ∈ eiPieces n D A v, PieceDec p := by
  simp only [eiOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hD, hA⟩, hv⟩ := h
  have fD := gpFacts hD
  have fA := gpFacts hA
  have hv2 : v < 2147483648 := hv
  refine ⟨?_, ?_⟩
  · cases n <;>
      simp (config := { decide := true }) [eiInstr, encodeLopn, eMnem, eiPieces, eiCmp, eOpB,
        fD.isGp, fA.isGp, hv2, stripWidthTag, adxPrefix, LprogBytes.rexW, setccCmpOp,
        encSetccCmpImm]
  · intro p hp
    simp only [eiPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact pieceDec_cmpImm A v hv
    · exact pieceDec_movZero D
    · exact pieceDec_setccE n D

/-- The address machine steps the materialised comparison with an immediate by writing the
    comparison bit `cmpBit` of the 64-bit value of `A` and the immediate to `D` at width
    `1`, keeping the zero flag. -/
theorem fstepA_seteImm (P : Params) (rsp : BitVec 64) (n : Bool) (D A : String) (v : Nat)
    (s : LstateA) (zf : Bool) {va : BitVec 64} (ha : s.reg.getW A 64 = some va) :
    fstepA (frameP P rsp) (eiInstr n D A v, .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D
          (VIR.JasminDialect.cmpBit (eRel n) va (BitVec.ofNat 64 v))).nextPc }, zf) := by
  cases n <;>
    simp (config := { decide := true }) [eiInstr, eMnem, eRel, fstepA, slotMov?, slotCmp?,
      regStepA, fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast,
      castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
      sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?,
      lsemStepN, readReg_of_getW ha, withALUFlags, aluFlagOp?, cellA?, slotCarry?,
      slotImm?, slotCmov?, evalOperandN, applyOpnN, cmpOfName?,
      show stripWidthTag "SETE:64" = "SETE" from by decide +kernel,
      show stripWidthTag "SETNE:64" = "SETNE" from by decide +kernel]

/-- **The machine run of a materialised comparison with an immediate.** The run writes to
    `D` the zero-extension of the comparison bit of the register of `A` and the immediate,
    keeps every other register, and keeps the memory. -/
theorem runBlock_eiPieces (sa : AState) (n : Bool) (D A : String) (v : Nat) :
    (∀ r, (aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)).regs r
      = if r = phys D then
          (VIR.JasminDialect.cmpBit (eRel n) (sa.regs (phys A)) (BitVec.ofNat 64 v)).setWidth 64
        else sa.regs r)
      ∧ (aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)).mem = sa.mem := by
  have hrun : aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)
      = evalInstrA (evalInstrA (evalInstrA sa (.cmp (phys A) (.imm v)))
          (.mov (phys D) (.imm 0))) (.setcc (if n then .ne else .e) (phys D)) := rfl
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by simp [eiPieces, noWriteB])⟩
  rw [hrun]
  by_cases hr : r = phys D
  · subst hr
    have hz := DecodedLsemStep.ZF_of_word_sub (sa.regs (phys A)) (BitVec.ofNat 64 v)
    cases n <;> by_cases he : sa.regs (phys A) = BitVec.ofNat 64 v <;>
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.setRegMerge, JState.flagB,
        JState.writeB5, JState.get, JState.condB, JOperand.eval, x86_SETcc, x86_CMP, x86_MOV,
        VIR.JasminDialect.cmpBit, eRel, x86_SUB, x86_eval_cond, hz, he, wordExtendMerge,
        VIR.JasminDialect.JasminCmp.holds] <;> decide
  · cases n <;>
      simp [evalInstrA, evalInstr, AState.view, JState.setReg, JState.setRegMerge,
        JState.writeB5, x86_MOV, hr]

/-- **The materialised comparison with an immediate.** From `ACorrW`, with `A` at width
    `64`, the address-machine step of `SET<cc>:64 D, [A, $v]`, which writes the comparison
    bit to `D` at width `1`, is matched by `cmp $v`, `mov $0` and `set<cc>`: the register of
    `D` holds the zero-extension of the bit. -/
theorem sim_seteImm (P : Params) (rsp : BitVec 64) (n : Bool) (D A : String) (v : Nat)
    (h : eiOk D A v = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwA : (s.reg.lvm A).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (eiInstr n D A v, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [eiOk, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, -⟩ := h
  rw [fstepA_seteImm P rsp n D A v s zf (hc.wide hA hwA)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hr, hm⟩ := runBlock_eiPieces sa n D A v
  refine ⟨hc.write hD _ hr (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_)
    (Or.inr ⟨_, ?_, rfl⟩), rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · simp [LstateN.nextPc, LstateN.setReg]

/-! ## 8l. The arithmetic right shift by an immediate -/

/-- The arithmetic right shift `SAR:64 D, [D, #k]` of `D` in place by the count `k`. -/
def rInstr (D : String) (k : Nat) : LinstrR := .Lopn [.reg D] "SAR:64" [.reg D, .imm k]

/-- The arithmetic right shift of a register name in place by an immediate, as `(D, k)`. -/
def classifyR : LinstrR → Option (String × Nat)
  | .Lopn [.reg d] m [.reg a, .imm k] => if m = "SAR:64" ∧ d = a then some (d, k) else none
  | _ => none

theorem classifyR_instr {i : LinstrR} {D : String} {k : Nat}
    (h : classifyR i = some (D, k)) : i = rInstr D k := by
  unfold classifyR at h
  split at h
  · split_ifs at h with h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

/-- **The conditions of an arithmetic right shift by an immediate** `SAR:64 D, [D, #k]`: a
    general-purpose name and a count `0 < k < 64`. -/
def rOk (D : String) (k : Nat) : Bool := gpOk D && decide (0 < k) && decide (k < 64)

/-- The bytes of `sar $k, %D` on the register numbered `n`: the shift-by-one form `D1 /7`
    for `k = 1`, the shift-by-`imm8` form `C1 /7 ib` otherwise. -/
def rBytes (n k : Nat) : List (BitVec 8) :=
  if k = 1 then encShift1 1 7 n else encShiftImmw 1 7 n k

/-- The byte piece of an arithmetic right shift by an immediate: `sar $k, %D`. -/
def rPieces (D : String) (k : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(rBytes (gpNumU D) k, .sar (phys D) (.imm k))]

/-- `sar $k, %D` with `k < 64` decodes to the arithmetic shift of the register of `D`. -/
theorem pieceDec_sarImm (D : String) (k : Nat) (hk : k < 64) :
    PieceDec (rBytes (gpNumU D) k, .sar (phys D) (.imm k)) := by
  intro rest
  by_cases h1 : k = 1
  · subst h1
    simpa [phys, rBytes] using
      decodeLinstr_shift1 7 (gpNumU D) rest (Or.inr (Or.inr rfl)) (gpNumU_lt_16 D)
  · simpa [phys, rBytes, h1] using
      decodeLinstr_shiftImm8 7 (gpNumU D) k rest (Or.inr (Or.inr rfl)) (gpNumU_lt_16 D)
        (by omega)

/-- **The bytes of an arithmetic right shift by an immediate.** -/
theorem rBytes_encode (P : Params) (D : String) (k : Nat) (h : rOk D k = true) :
    encodeLopn P.frame P.spillW (rInstr D k) P.qsaveB = (rPieces D k).flatMap Prod.fst
      ∧ ∀ p ∈ rPieces D k, PieceDec p := by
  simp only [rOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hD, -⟩, hk⟩ := h
  have fD := gpFacts hD
  refine ⟨?_, ?_⟩
  · simp only [rInstr, encodeLopn, LprogAsmPrinter.isCarryOutBinding,
      LprogAsmPrinter.isMulHiBinding, stripWidthTag, LprogAsmPrinter.mnemWidth, adxPrefix,
      hasSuffix, LprogBytes.rexW]
    simp (config := { decide := true }) [encImmOp, fD.notSlot, shiftImmExt, rPieces, rBytes]
  · intro p hp
    simp only [rPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact pieceDec_sarImm D k hk

/-- The address machine steps the arithmetic right shift by an immediate by writing the
    arithmetic shift of the 64-bit value of `D` by a count `k < 64` to `D`, keeping the
    zero flag. -/
theorem fstepA_sarImm (P : Params) (rsp : BitVec 64) (D : String) (k : Nat) (hk : k < 64)
    (s : LstateA) (zf : Bool) {v : BitVec 64} (hv : s.reg.getW D 64 = some v) :
    fstepA (frameP P rsp) (rInstr D k, .reg none) s zf
      = some ({ s with reg := (s.reg.setReg D (BitVec.sshiftRight v k)).nextPc }, zf) := by
  simp (config := { decide := true }) [Nat.mod_eq_of_lt hk, rInstr, fstepA, slotMov?, slotCmp?,
    regStepA, fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast,
    castStruct?, movImmStruct?, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
    sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh, VIR.JasminLsemShift.sarStruct?,
    readReg_of_getW hv, withALUFlags, aluFlagOp?, cellA?, slotCarry?,
    slotImm?, slotCmov?]

/-- The data word of `x86_SAR` by an immediate count `0 < k < 64` is the arithmetic shift
    by `k`. -/
theorem x86_SAR_word_imm (v : BitVec 64) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) :
    (x86_SAR v (BitVec.ofNat 64 k)).word = BitVec.sshiftRight v k := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [x86_SAR, shiftCount, hkn, VIR.shiftMask_of_lt hk, ite_eq_right hk0, rflags_OF, wsar,
    Nat.min_eq_right hk.le]

/-- **The machine run of an arithmetic right shift by an immediate.** The run writes to `D`
    the arithmetic shift of its register by `k`, keeps every other register, and keeps the
    memory. -/
theorem runBlock_rPieces (sa : AState) (D : String) (k : Nat) (hk0 : 0 < k) (hk : k < 64) :
    (∀ r, (aMachine.runBlock sa ((rPieces D k).map Prod.snd)).regs r
      = if r = phys D then BitVec.sshiftRight (sa.regs (phys D)) k else sa.regs r)
      ∧ (aMachine.runBlock sa ((rPieces D k).map Prod.snd)).mem = sa.mem := by
  have hrun : aMachine.runBlock sa ((rPieces D k).map Prod.snd)
      = evalInstrA sa (.sar (phys D) (.imm k)) := rfl
  refine ⟨fun r => ?_, runBlock_mem_of_noWriteB _ sa (by simp [rPieces, noWriteB])⟩
  rw [hrun]
  by_cases hr : r = phys D
  · subst hr
    simp [evalInstrA, evalInstr, AState.view, JState.writeB5W, JState.get, JOperand.eval,
      x86_SAR_word_imm _ k (by omega) hk]
  · simp [evalInstrA, evalInstr, AState.view, JState.writeB5W, hr]

/-- **The arithmetic right shift by an immediate.** From `ACorrW`, with `D` at width `64`,
    the address-machine step of `SAR:64 D, [D, #k]` is matched by `sar $k`: the register of
    `D` holds the shifted word. -/
theorem sim_sarImm (P : Params) (rsp : BitVec 64) (D : String) (k : Nat)
    (h : rOk D k = true) (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s)
    (hwD : (s.reg.lvm D).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) (rInstr D k, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((rPieces D k).map Prod.snd)) s' ∧ zf' = zf := by
  simp only [rOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hD, hk0⟩, hk⟩ := h
  rw [fstepA_sarImm P rsp D k hk s zf (hc.wide hD hwD)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hr, hm⟩ := runBlock_rPieces sa D k hk0 hk
  refine ⟨hc.write hD _ hr (fun x hx => by rw [hm]; exact hc.mem x hx) (fun r hr' => ?_)
    (Or.inl ?_), rfl⟩
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr']
  · exact (getW_setReg_nextPcN _ D D _).trans (ite_eq_left rfl)

/-- An instruction other than the closing return of a printed body with carry chains: an
    `Lopn` read into a width-carrying cast between general-purpose names, a carry constant, a
    slot carry arm, a carry arm, a cell arm, an immediate
    store into a frame slot, a wide immediate, a register select, a select with a slot true
    value, a select with a slot false value, a materialised comparison against a register or
    an immediate, a register-count shift, an arithmetic right shift by an immediate or an arm of
    `DecodePrintedAddr` whose conditions hold, a label, or a conditional branch on the zero
    flag to a label the body defines. -/
def instrOKWB (body : Lcmd) (P : Params) : LinstrR → Bool
  | .Lopn ds o ss =>
      match classifyK (.Lopn ds o ss) with
      | some (d, a, _, _) => castOk d a
      | none =>
      match movImmStruct? (.Lopn ds o ss) with
      | some (d, n) => imm32Ok d n
      | none =>
      match classifyS (.Lopn ds o ss) with
      | some c => c.ok P
      | none =>
      match classifyC (.Lopn ds o ss) with
      | some c => c.ok
      | none =>
          match classifyM (.Lopn ds o ss) with
          | some m => m.ok
          | none =>
              match classifyI (.Lopn ds o ss) with
              | some (q, v) => iOk P q v
              | none =>
              match classifyL (.Lopn ds o ss) with
              | some (d, v) => lOk d v
              | none =>
              match classifyV (.Lopn ds o ss) with
              | some (d, c, a, b) => vOk d c a b || (vtOk P d c a b || vfOk P d c a b)
              | none =>
              match classifyE (.Lopn ds o ss) with
              | some (_, d, a, b) => eOk d a b
              | none =>
              match classifyX (.Lopn ds o ss) with
              | some (_, d, a, b) => xOk d a b
              | none =>
              match classifyEI (.Lopn ds o ss) with
              | some (_, d, a, v) => eiOk d a v
              | none =>
              match classifyR (.Lopn ds o ss) with
              | some (d, k) => rOk d k
              | none =>
                  match classifyA (.Lopn ds o ss) with
                  | some a => a.ok P
                  | none => false
  | .Llabel _ _ => true
  | .Lcond (.reg cc) l => (condPol cc).isSome && (labelAt body l).isSome
  | _ => false

/-- A carry-out binding `ADCXHI:64 O, A, S, C` at position `k` directly follows the add
    `ADCX:64 D, A, S, C` on the same sources, whose destination is none of them and, as a
    slot, has a frame word disjoint from those of slot sources and of a slot carry-in. -/
def carryPrevB (body : Lcmd) (k : Nat) : Bool :=
  match body[k]? with
  | some ⟨_, .Lopn [.reg _] o [.reg a, .reg s, .reg c]⟩ =>
      if o = "ADCXHI:64" then
        k != 0 && (match body[k - 1]? with
          | some ⟨_, .Lopn [.reg d] o' [.reg a', .reg s', .reg c']⟩ =>
              o' == "ADCX:64" && a == a' && s == s' && c == c' && d != a && d != s && d != c
                && slotSepB (Params.ofBody body) d a && slotSepB (Params.ofBody body) d s
                && slotSepB (Params.ofBody body) d c
          | _ => false)
      else true
  | _ => true

/-- **The covered printed bodies with carry chains**: decodable, ending in the return, every
    other instruction a carry arm, an untagged immediate move or in the fragment of
    `DecodePrintedCFG`, every conditional branch directly after a compare, every carry-out
    binding directly after its add, and every cast keeping the low bits its source and
    destination widths give (`castPosB`). An untagged immediate move is a carry constant where
    `bitMovB` holds and a 32-bit constant otherwise. -/
def printedAddrWB (body : Lcmd) : Bool :=
  decodableLcmd body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i)
    && (List.range body.length).all (condPrevB body)
    && (List.range body.length).all (carryPrevB body)
    && (List.range body.length).all (castPosB body)

/-- `carryPrevB` with the body parameters `P` given as an argument. -/
def carryPrevBWith (P : Params) (body : Lcmd) (k : Nat) : Bool :=
  match body[k]? with
  | some ⟨_, .Lopn [.reg _] o [.reg a, .reg s, .reg c]⟩ =>
      if o = "ADCXHI:64" then
        k != 0 && (match body[k - 1]? with
          | some ⟨_, .Lopn [.reg d] o' [.reg a', .reg s', .reg c']⟩ =>
              o' == "ADCX:64" && a == a' && s == s' && c == c' && d != a && d != s && d != c
                && slotSepB P d a && slotSepB P d s && slotSepB P d c
          | _ => false)
      else true
  | _ => true

/-- `carryPrevB` is `carryPrevBWith` at the parameters of the body. -/
theorem carryPrevB_eq_with (body : Lcmd) :
    carryPrevB body = carryPrevBWith (Params.ofBody body) body := rfl

/-- `carryPrevBWith` over a body held as an array, indexed in constant time. -/
def carryPrevBA (P : Params) (body : Array Linstr) (k : Nat) : Bool :=
  match body[k]? with
  | some ⟨_, .Lopn [.reg _] o [.reg a, .reg s, .reg c]⟩ =>
      if o = "ADCXHI:64" then
        k != 0 && (match body[k - 1]? with
          | some ⟨_, .Lopn [.reg d] o' [.reg a', .reg s', .reg c']⟩ =>
              o' == "ADCX:64" && a == a' && s == s' && c == c' && d != a && d != s && d != c
                && slotSepB P d a && slotSepB P d s && slotSepB P d c
          | _ => false)
      else true
  | _ => true

/-- `carryPrevBA` at the array of a body is `carryPrevBWith`. -/
theorem carryPrevBA_toArray (P : Params) (body : Lcmd) :
    carryPrevBA P body.toArray = carryPrevBWith P body := by
  funext k
  simp only [carryPrevBA, carryPrevBWith, List.getElem?_toArray]

/-- `printedAddrWB` evaluated with the body parameters `Params.ofBody body` computed once for
    the instruction gates `instrOKWB` and the carry-out gates, the carry-out gates and the cast
    gates read off the array of the body, and the cast width analyses read off
    `narrowTable`. -/
def printedAddrWBImpl (body : Lcmd) : Bool :=
  let P := Params.ofBody body
  let a := body.toArray
  decodableLcmd body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => instrOKWB body P i.li_i)
    && (List.range a.size).all (condPrevBA a)
    && (List.range a.size).all (carryPrevBA P a)
    && (List.range a.size).all (castPosBA a (narrowTable body))

/-- The gate `printedAddrWB` is evaluated as `printedAddrWBImpl`. -/
@[csimp] theorem printedAddrWB_eq_impl : @printedAddrWB = @printedAddrWBImpl := by
  funext body
  simp only [printedAddrWB, printedAddrWBImpl, List.size_toArray, carryPrevBA_toArray,
    castPosBA_toArray, carryPrevB_eq_with, condPrevBA_toArray]

/-- **The count-`0` shift of a general-purpose name in place is covered**: `instrOKWB`
    accepts `SHL:64 R, R, #0`, the copy of `R` to itself, for every general-purpose name `R`,
    every body and all body parameters. -/
theorem instrOKWB_shl0 (body : Lcmd) (P : Params) {R : String} (hR : gpOk R = true) :
    instrOKWB body P (.Lopn [.reg R] "SHL:64" [.reg R, .imm 0]) = true := by
  have hm := mem_gpList hR
  simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

/-- The instruction conjunct of `printedAddrWB`: it holds of a body each of whose
    instructions before the last is a count-`0` shift `SHL:64 R, R, #0` of a general-purpose
    name `R` in place or passes `instrOKWB`. -/
theorem instrOKWB_all_of_shl0 {body : Lcmd}
    (h : ∀ i ∈ body.dropLast, (∃ R, gpOk R = true
        ∧ i.li_i = .Lopn [.reg R] "SHL:64" [.reg R, .imm 0])
      ∨ instrOKWB body (Params.ofBody body) i.li_i = true) :
    body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i) = true := by
  rw [List.all_eq_true]
  intro i hi
  rcases h i hi with ⟨R, hR, he⟩ | hok
  · rw [he]
    exact instrOKWB_shl0 body _ hR
  · exact hok

/-- **The materialised comparison over general-purpose names is covered**: `instrOKWB`
    accepts `SETE:64 R, [A, B]` and `SETNE:64 R, [A, B]` for all general-purpose names `R`,
    `A`, `B`, every body and all body parameters. -/
theorem instrOKWB_sete (body : Lcmd) (P : Params) (n : Bool) {R A B : String}
    (hR : gpOk R = true) (hA : gpOk A = true) (hB : gpOk B = true) :
    instrOKWB body P (eInstr n R A B) = true := by
  cases n <;>
    simp (config := { decide := true }) [instrOKWB, eInstr, eMnem, classifyK, movImmStruct?,
      classifyS, classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, eOk, hR, hA,
      hB]

/-- **The register-count shift over general-purpose names is covered**: `instrOKWB` accepts
    `SHL:64 R, [A, B]` and `SHR:64 R, [A, B]` for all general-purpose names `R`, `A`, `B`,
    every body and all body parameters. -/
theorem instrOKWB_shrReg (body : Lcmd) (P : Params) (l : Bool) {R A B : String}
    (hR : gpOk R = true) (hA : gpOk A = true) (hB : gpOk B = true) :
    instrOKWB body P (xInstr l R A B) = true := by
  cases l <;>
    simp (config := { decide := true }) [instrOKWB, xInstr, xMnem, classifyK, movImmStruct?,
      classifyS, classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX,
      xOk, hR, hA, hB]

/-- **The materialised comparison with an immediate is covered**: `instrOKWB` accepts
    `SETE:64 R, [A, $v]` and `SETNE:64 R, [A, $v]` for all general-purpose names `R`, `A`,
    every immediate `v < 2^31`, every body and all body parameters. -/
theorem instrOKWB_seteImm (body : Lcmd) (P : Params) (n : Bool) {R A : String} {v : Nat}
    (hR : gpOk R = true) (hA : gpOk A = true) (hv : v < 2 ^ 31) :
    instrOKWB body P (eiInstr n R A v) = true := by
  have hv2 : v < 2147483648 := hv
  cases n <;>
    simp (config := { decide := true }) [instrOKWB, eiInstr, eMnem, classifyK, movImmStruct?,
      classifyS, classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX,
      classifyEI, eiOk, hR, hA, hv2]

/-- **The arithmetic right shift by an immediate is covered**: `instrOKWB` accepts
    `SAR:64 R, [R, #k]` for every general-purpose name `R`, every count `0 < k < 64`, every
    body and all body parameters. -/
theorem instrOKWB_sarImm (body : Lcmd) (P : Params) {R : String} {k : Nat}
    (hR : gpOk R = true) (hk0 : 0 < k) (hk : k < 64) :
    instrOKWB body P (rInstr R k) = true := by
  simp (config := { decide := true }) [instrOKWB, rInstr, classifyK, movImmStruct?,
    classifyS, classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX,
    classifyEI, classifyR, rOk, hR, hk0, hk]

/-- The source of a frame-word store `m q, S` at the program counter of `s` (`slotMov?`, `q`
    neither a general-purpose name nor a cell name `mem.B.off`), or of a copy `m q, S` between
    general-purpose names, when `S` holds a one-bit value in `s`. -/
def bitSrc (body : Lcmd) (s : LstateA) : List String :=
  match body[s.reg.lpc]? with
  | some i =>
      match slotMov? i.li_i with
      | some (q, S) =>
          if !hasPrefix q "mem." && (!gpOk q || gpOk S) && (s.reg.lvm S).1 == 1 then [S]
          else []
      | none => []
  | none => []

/-- A name of `bitSrc` is the one-bit source of a frame-word store at the program counter. -/
theorem bitSrc_spec {body : Lcmd} {s : LstateA} {r : String} (h : r ∈ bitSrc body s) :
    ∃ i q b, body[s.reg.lpc]? = some i ∧ slotMov? i.li_i = some (q, r)
      ∧ (gpOk q = false ∨ gpOk r = true)
      ∧ hasPrefix q "mem." = false ∧ s.reg.lvm r = ⟨1, b⟩ := by
  unfold bitSrc at h
  split at h
  · rename_i i hi
    split at h
    · rename_i q S hm
      split at h
      · rename_i hc
        simp only [List.mem_singleton] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.or_eq_true] at hc
        obtain ⟨⟨hcp, hq⟩, hw⟩ := hc
        generalize hr : s.reg.lvm r = c at hw
        obtain ⟨w, v⟩ := c
        simp only at hw
        subst hw
        exact ⟨i, q, v, hi, hm, hq, hcp, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-- At an instruction that is no frame-word move, `bitSrc` is empty. -/
theorem not_mem_bitSrc {body : Lcmd} {s : LstateA} {i : Linstr}
    (hi : body[s.reg.lpc]? = some i) (hm : slotMov? i.li_i = none) (r : String) :
    r ∉ bitSrc body s := by
  intro h
  obtain ⟨i', q, b, hi', hm', -⟩ := bitSrc_spec h
  rw [hi] at hi'
  cases hi'
  rw [hm] at hm'
  cases hm'

/-- At the program counter of `s`, every general-purpose name the instruction reads, other
    than a carry-in, the source of a cast with an entry in the cast width analysis
    (`narrowSrc`) and the one-bit source of a frame-word store (`bitSrc`), holds a 64-bit
    value. -/
def WideSafeAt (body : Lcmd) (s : LstateA) : Prop :=
  ∀ ii ds o ss, body[s.reg.lpc]? = some ⟨ii, .Lopn ds o ss⟩ →
    ∀ r, readsI (.Lopn ds o ss) r → gpOk r = true → r ∉ carryIns (.Lopn ds o ss) →
      r ∉ narrowSrc body s.reg.lpc ++ bitSrc body s → (s.reg.lvm r).1 = 64

/-- At the program counter of `s`, a cell load (`cellA?`, the forms `LOAD:64 D, n` and
    `MOV:64 D, n` with `n` a cell name) reads eight bytes disjoint from the red-zone word at
    `rsp`. -/
def CellSafeAt (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  ∀ ii x D B off p, body[s.reg.lpc]? = some ⟨ii, x⟩ → cellA? x = some (.ld D B off) →
    s.reg.getW B 64 = some p → Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off)

/-- The run safety of a body with carry chains and cells: safe indexed loads, every
    general-purpose name read besides a carry-in at width `64`, and safe cell loads. -/
def SafeW (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  LoadSafeAt rsp body s ∧ WideSafeAt body s ∧ CellSafeAt rsp body s

/-- `SafeW` with the cast width analysis (`NarrowInv`). -/
def SafeWN (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  LoadSafeAt rsp body s ∧ WideSafeAt body s ∧ CellSafeAt rsp body s ∧ NarrowInv body s

/-- A run that is safe in the sense of `SafeW` from a state satisfying `NarrowInv` is safe in
    the sense of `SafeWN`. -/
theorem runSafe_narrow {frame : String → Option (BitVec 64)} {rsp : BitVec 64} {body : Lcmd} :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool), NarrowInv body s →
      RunSafe frame body (SafeW rsp body) fuel s zf →
      RunSafe frame body (SafeWN rsp body) fuel s zf
  | 0, _, _, _, _ => trivial
  | fuel + 1, _, _, hI, h =>
      ⟨⟨h.1.1, h.1.2.1, h.1.2.2, hI⟩, fun s' zf' hst =>
        runSafe_narrow fuel s' zf' (narrowInv_step hI hst) (h.2 s' zf' hst)⟩

/-- At position `k` a carry-out binding finds the carry-out of its add in the machine carry
    flag. -/
def CarryReq (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) (sa : AState)
    (s : LstateA) : Prop :=
  ∀ ii O A S C, body[k]? = some ⟨ii, .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]⟩ →
    CarryAt frame sa s A S C

/-- The facts of a body in the class `printedAddrWB` that the simulation reads. -/
structure BodyFactsW (body : Lcmd) (shs : List DShape) : Prop where
  /-- The shapes of the body. -/
  shapes : shapesOf (Params.ofBody body) body = some shs
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret
  /-- Every other instruction is covered. -/
  instr : ∀ k (hk : k + 1 < body.length),
    instrOKWB body (Params.ofBody body) (body[k]'(by omega)).li_i = true
  /-- Every conditional branch follows a compare. -/
  cond : ∀ k, k < body.length → condPrevB body k = true
  /-- Every carry-out binding follows its add. -/
  carry : ∀ k, k < body.length → carryPrevB body k = true
  /-- Every cast keeps the low bits its source and destination widths give. -/
  cast : ∀ k, k < body.length → castPosB body k = true

/-- The facts of a printed body with carry chains that may hold remote transfers, which the
    per-step simulation `step_simWN` reads: those of `BodyFactsW`, with every instruction before
    the last either a remote transfer (`remoteSym`) or covered. -/
structure BodyFactsCW (body : Lcmd) (shs : List DShape) : Prop where
  /-- The shapes of the body. -/
  shapes : shapesOf (Params.ofBody body) body = some shs
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret
  /-- Every other instruction is a remote transfer or covered. -/
  instr : ∀ k (hk : k + 1 < body.length),
    remoteSym (body[k]'(by omega)).li_i ≠ none
      ∨ instrOKWB body (Params.ofBody body) (body[k]'(by omega)).li_i = true
  /-- Every conditional branch follows a compare. -/
  cond : ∀ k, k < body.length → condPrevB body k = true
  /-- Every carry-out binding follows its add. -/
  carry : ∀ k, k < body.length → carryPrevB body k = true
  /-- Every cast keeps the low bits its source and destination widths give. -/
  cast : ∀ k, k < body.length → castPosB body k = true

/-- A body with the facts `BodyFactsW` has the facts `BodyFactsCW`. -/
theorem BodyFactsW.toCW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) :
    BodyFactsCW body shs :=
  ⟨hF.shapes, hF.pos, hF.last, fun k hk => .inr (hF.instr k hk), hF.cond, hF.carry, hF.cast⟩

theorem acorrW_setLpc {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    (p : Nat) : ACorrW rsp sa (s.setLpc p) :=
  ⟨h.regs, h.sp, h.mem⟩

theorem haltedA_eq_falseW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    {s : LstateA} {k : Nat} (hpc : s.reg.lpc = k) (hk : k + 1 < body.length) :
    haltedA body s = false := by
  have hok := hF.instr k hk
  unfold haltedA
  rw [hpc, List.getElem?_eq_getElem (by omega)]
  revert hok
  rcases body[k] with ⟨ii, li⟩
  cases li <;> simp [instrOKWB]

/-- The instruction after one that is no add is no carry-out binding, in a body that may hold
    remote transfers. -/
theorem no_carryReqC {body : Lcmd} {shs : List DShape} (hF : BodyFactsCW body shs) {k : Nat}
    (hk : k + 1 < body.length) (h : ∀ ii d a s c, body[k]? ≠
      some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩)
    (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA) :
    CarryReq frame body (k + 1) sa s := by
  intro ii O A S C hb
  have hc := hF.carry (k + 1) hk
  unfold carryPrevB at hc
  rw [hb] at hc
  simp only [ite_true, Nat.add_sub_cancel] at hc
  split at hc
  · next ii' d o' a' s' c' heq =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨ho, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hc
    subst ho
    exact absurd heq (h ii' d a' s' c')
  · simp at hc

/-- The instruction after one that is no add is no carry-out binding. -/
theorem no_carryReq {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) {k : Nat}
    (hk : k + 1 < body.length) (h : ∀ ii d a s c, body[k]? ≠
      some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩)
    (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA) :
    CarryReq frame body (k + 1) sa s :=
  no_carryReqC hF.toCW hk h frame sa s

/-- A carry-out binding is required at a label. -/
theorem carryReq_label {body : Lcmd} {k : Nat} {ii : Nat} {kd : LabelKind} {l : LLabel}
    (hb : body[k]? = some ⟨ii, .Llabel kd l⟩) (frame : String → Option (BitVec 64))
    (sa : AState) (s : LstateA) : CarryReq frame body k sa s := by
  intro ii' O A S C h
  rw [hb] at h
  simp at h

/-- `normA` keeps the implicit read of `RDX`. -/
theorem readsRdx_normA (i : LinstrR) : readsRdx (normA i) = readsRdx i := by
  cases i with
  | Lopn ds o ss =>
    simp only [normA, readsRdx, rdxOp]
    by_cases h : LprogAsmPrinter.untagCaret o = "MULX"
    · simp [h, LprogAsmPrinter.untagCaret_of_caret_free
        (by decide +kernel : '^' ∉ (withWidthTag 64 "MULX").toList)]
    · simp [h, VIR.JasminLsemAddrCongr.untagCaret_idem]
  | _ => rfl

/-- The readsI of `normA i` are those of `i`. -/
theorem readsI_normA (i : LinstrR) (r : String) : readsI (normA i) r ↔ readsI i r := by
  cases i <;> simp only [readsI, readsRdx_normA] <;> simp [normA]

/-- The mnemonic of an address-machine arm whose conditions hold has no `^`. -/
theorem AArm.instr_caret_free {P : Params} {a : AArm} (h : a.ok P = true)
    {ds : List LOperand} {o : String} {ss : List LOperand}
    (he : a.instr = .Lopn ds o ss) : '^' ∉ o.toList := by
  cases a with
  | reg a =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    exact Arm.caret_free_of_ok h.1.2 he
  | st m q S =>
    simp only [AArm.ok, Bool.and_eq_true, isMovM, Bool.or_eq_true, beq_iff_eq] at h
    simp only [AArm.instr, LinstrR.Lopn.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    rcases h.2 with rfl | rfl <;> decide
  | ld m D q =>
    simp only [AArm.ok, Bool.and_eq_true, isMovM, Bool.or_eq_true, beq_iff_eq] at h
    simp only [AArm.instr, LinstrR.Lopn.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    rcases h.2 with rfl | rfl <;> decide
  | _ =>
    all_goals (simp only [AArm.instr, LinstrR.Lopn.injEq] at he; obtain ⟨-, rfl, -⟩ := he; decide)

/-- An instruction on three register sources is no compare arm. -/
theorem classifyA_three_not_cmp (d m : String) (a s c : String) :
    (classifyA (.Lopn [.reg d] m [.reg a, .reg s, .reg c])).any cmpArmB = false := by
  simp [classifyA, cmpArmB, Option.any_map]

/-- The decoded instructions of an `Lopn` at position `k`, in any program that holds them from
    the index of `k`, run from that index to the decoded index of `k + 1`. -/
theorem reaches_blockP {body : Lcmd} {shs : List DShape} {prog : List RInstr} {k : Nat}
    (hks : k < shs.length)
    (hP : ∃ A B, prog = A ++ blkOf body shs shs[k] ++ B ∧ A.length = posOf shs k)
    {ds : List LOperand} {o : String} {ss : List LOperand}
    (hshk : shapeOf (Params.ofBody body) (.Lopn ds o ss) = some shs[k]) {js : List (JInstr 64)}
    (hops : shs[k].ops' = js) (sa : AState) :
    Reaches aMachine prog (posOf shs k) sa (posOf shs (k + 1)) (aMachine.runBlock sa js) := by
  obtain ⟨A, B, hsplit, hA⟩ := hP
  obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
  have hprog : prog = A ++ js.map RInstr.op ++ B := by
    rw [hsplit, hblk, hops]
  have h0 := reaches_ops aMachine A js B sa
  rw [← hprog, hA] at h0
  have hpos : posOf shs (k + 1) = posOf shs k + js.length := by
    rw [posOf_succ shs k hks, hn, hops]
  rw [hpos]
  exact h0

/-- The decoded instructions of an `Lopn` at position `k` run from its decoded index to the
    decoded index of `k + 1`. -/
theorem reaches_block {body : Lcmd} {shs : List DShape} (a b : JInstr 64) {k : Nat}
    (hks : k < shs.length) {ds : List LOperand} {o : String} {ss : List LOperand}
    (hshk : shapeOf (Params.ofBody body) (.Lopn ds o ss) = some shs[k]) {js : List (JInstr 64)}
    (hops : shs[k].ops' = js) {sa : AState} {e : Nat} {sa' : AState}
    (hR : Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
      (posOf shs (k + 1)) (aMachine.runBlock sa js) e sa') :
    Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
      (posOf shs k) sa e sa' :=
  (reaches_blockP hks (prog_split body shs a b k hks) hshk hops sa).trans hR

/-- The instruction at position `k` of a body. -/
theorem body_get {body : Lcmd} {k : Nat} (hk : k < body.length) :
    body[k]? = some (body[k]'hk) := List.getElem?_eq_getElem hk

/-- **A register copy on the address machine.** A move between names without a frame word
    (`slotMov?`) writes the value of the source, at its width, to the destination. -/
theorem fstepA_regCopy (frame : String → Option (BitVec 64)) {x : LinstrR} {d q : String}
    (h : slotMov? x = some (d, q)) (hq : frame q = none) (hd : frame d = none) (sa : LstateA)
    (zf : Bool) :
    fstepA frame (x, .reg none) sa zf
      = some ({ sa with reg := (sa.reg.setReg d (sa.reg.lvm q).2).nextPc }, zf) := by
  have hx : x = .Lopn [.reg d] "MOVQ" [.reg q] ∨ x = .Lopn [.reg d] "MOV:64" [.reg q] := by
    unfold slotMov? at h
    split at h
    · split_ifs at h with hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases h
  have hc : cmpArgs? (x, MemTag.reg none) = none := by
    rcases hx with rfl | rfl <;> rfl
  have hm : movRegArgs? (x, MemTag.reg none) = some (d, q) := by
    rcases hx with rfl | rfl
    · simp only [movRegArgs?, show stripWidthTag "MOVQ" = "MOVQ" by decide +kernel]
      rfl
    · simp only [movRegArgs?, show stripWidthTag "MOV:64" = "MOV" by decide +kernel]
      rfl
  simp only [fstepA, h, hq, hd, regStepA, fstepF, hc, hm]
  rfl

/-- **The copy of a one-bit name.** An arm whose instruction is a copy `m q, S` between
    general-purpose names, with `S` holding the bit `b`, gives `q` the bit on the address
    machine; the machine copies the register of `S`, which holds the zero-extension of `b`, so
    `ACorrW` relates `q` to the machine register of `q` after the decoded instructions. Every
    other name keeps its machine register, read off the step from the widened state. -/
theorem AArm.simW_copy1 (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true)
    {q S : String} (hli : a.li = (a.li.fst, .reg none))
    (hmv : slotMov? a.li.fst = some (q, S)) (hq : gpOk q = true) (hS : gpOk S = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hsafe : a.LoadSafe rsp (widenS sa s))
    (hc : ACorrW rsp sa s) {b : BitVec 1}
    (hb : s.reg.lvm S = ⟨1, b⟩) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) a.li s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (a.js P)) s' := by
  have hphys : sa.regs (phys S) = b.setWidth 64 := by
    rcases hc.regs S hS with h1 | ⟨b', h1, h2⟩ | h1
    · rw [getW_eq_some_iff, hb] at h1; cases h1
    · rw [hb] at h1
      obtain ⟨-, h1⟩ := Sigma.mk.inj_iff.mp h1
      rw [h2, eq_of_heq h1]
    · have := h1.width; rw [hb] at this; simp at this
  obtain ⟨t', zt, h1, h2, -⟩ := AArm.sim P rsp a h sa (widenS sa s) zf hc.widen hsafe
  rw [hli, fstepA_regCopy (frameP P rsp) hmv (frameP_gp hS) (frameP_gp hq)] at hst h1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h1)
  have hwS : (widenS sa s).reg.lvm S = ⟨64, b.setWidth 64⟩ := by
    show widenCell S (sa.regs (phys S)) (s.reg.lvm S) = _
    simp [widenCell, hb, hS, narrowW, hphys]
  refine ⟨fun r hr => ?_, h2.sp, fun x hx => ?_⟩
  · have hM := h2.regs r hr
    by_cases hrq : r = q
    · rw [hrq] at hM ⊢
      refine Or.inr (Or.inl ⟨b, by simp [LstateN.setReg, LstateN.nextPc, hb], ?_⟩)
      have e : ((widenS sa s).reg.setReg q ((widenS sa s).reg.lvm S).2).nextPc.lvm q
          = ⟨64, b.setWidth 64⟩ := by
        simp only [LstateN.setReg, LstateN.nextPc, ite_true]
        exact hwS
      rw [getW_eq_some_iff] at hM
      rw [e] at hM
      exact (eq_of_heq (Sigma.mk.inj_iff.mp hM).2).symm
    · have hw : (widenS sa s).reg.lvm r = ⟨64, sa.regs (phys r)⟩ := by
        show widenCell r (sa.regs (phys r)) (s.reg.lvm r) = _
        apply widenCell_of_regs hr
        rcases hc.regs r hr with hg | hb' | hn
        · exact Or.inl (lvm_of_getW hg)
        · exact Or.inr (Or.inl hb')
        · exact Or.inr (Or.inr hn)
      have hreg : (aMachine.runBlock sa (a.js P)).regs (phys r) = sa.regs (phys r) := by
        rw [getW_eq_some_iff] at hM
        simp only [LstateN.setReg, LstateN.nextPc, hrq, ite_false, hw] at hM
        exact (eq_of_heq (Sigma.mk.inj_iff.mp hM).2).symm
      have hl : ((s.reg.setReg q (s.reg.lvm S).2).nextPc).lvm r = s.reg.lvm r := by
        simp [LstateN.setReg, LstateN.nextPc, hrq]
      have hg : ((s.reg.setReg q (s.reg.lvm S).2).nextPc).getW r 64 = s.reg.getW r 64 := by
        unfold LstateN.getW
        rw [hl]
      rw [hreg, hg, hl]
      exact hc.regs r hr
  · rw [← h2.mem x hx]
    rfl

/-- **One step on both machines, with carry chains.** Let `prog` hold the decoded instructions
    of position `k` of a body with the facts `BodyFactsCW` from the decoded index of `k`. A
    step of the address machine at `k`, from states related by `ACorrW`, with the machine zero
    flag equal to the flag at a conditional branch, the machine carry flag holding the
    carry-out at a carry-out binding, and the safety `SafeWN` of the start state, is matched by
    a path of the machine on `prog` from the index of `k` to the index of the reached position.
    The reached states are related by `ACorrW`, and the zero and carry conditions hold at the
    reached position. A remote transfer takes no step of the address machine. -/
theorem step_simWN {body : Lcmd} {shs : List DShape} (hF : BodyFactsCW body shs)
    (rsp : BitVec 64) {prog : List RInstr} {k : Nat}
    (hprog : ∀ hs : k < shs.length,
      ∃ A B, prog = A ++ blkOf body shs shs[k] ++ B ∧ A.length = posOf shs k)
    (sa : AState) (s : LstateA) (zf : Bool) (s' : LstateA) (zf' : Bool)
    (hpc : s.reg.lpc = k) (hk : k < body.length) (hkn : k + 1 < body.length)
    (hc : ACorrW rsp sa s)
    (hz : isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf)
    (hcy : CarryReq (frameP (Params.ofBody body) rsp) body k sa s)
    (hsafe : SafeWN rsp body s)
    (hst : stepA (frameP (Params.ofBody body) rsp) body s zf = some (s', zf')) :
    ∃ sb, Reaches aMachine prog (posOf shs k) sa (posOf shs s'.reg.lpc) sb ∧ ACorrW rsp sb s'
      ∧ ∃ hl : s'.reg.lpc < body.length,
        (isCondB (body[s'.reg.lpc]'hl).li_i = true → sb.flags.zf.getD false = zf')
          ∧ CarryReq (frameP (Params.ofBody body) rsp) body s'.reg.lpc sb s' := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  obtain ⟨hl, hsh⟩ := shapesOf_spec P body shs hF.shapes
  have hok0 := hF.instr k hkn
  have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
    rw [hpc]; exact List.getElem?_eq_getElem hk
  have hks : k < shs.length := by omega
  have hshk := hsh k hk hks
  have hblk := hprog hks
  -- an instruction other than an add leaves no carry-out binding next
  have hnoadd : (∀ ii d a s c, body[k]? ≠
      some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩) →
      ∀ sa s, CarryReq frame body (k + 1) sa s :=
    fun h sa s => no_carryReqC hF hkn h frame sa s
  -- a conditional branch next follows a compare arm
  have hcondNext : isCondB (body[k + 1]'hkn).li_i = true →
      ((classifyA (body[k]'hk).li_i).any cmpArmB) = true := by
    intro hcnd
    have hc2 := hF.cond (k + 1) hkn
    unfold condPrevB at hc2
    rw [List.getElem?_eq_getElem hkn] at hc2
    revert hc2 hcnd
    rcases body[k + 1] with ⟨ii', li'⟩
    cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk]
  rcases hbk : body[k]'hk with ⟨ii, li⟩
  rw [hbk] at hok0 hget hshk hz hcondNext
  simp only at hok0 hshk hz hcondNext
  have hbk? : body[k]? = some ⟨ii, li⟩ := by rw [body_get hk, hbk]
  cases li with
    | Lopn ds o ss =>
      have hok : instrOKWB body P (.Lopn ds o ss) = true := hok0.resolve_left (fun h => h rfl)
      -- the decoded block of the instruction and the conditions at the next position
      have hnext : ∀ js : List (JInstr 64), shs[k].ops' = js → s'.reg.lpc = k + 1 →
          ACorrW rsp (aMachine.runBlock sa js) s' →
          (isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa js).flags.zf.getD false = zf') →
          CarryReq frame body (k + 1) (aMachine.runBlock sa js) s' →
          ∃ sb, Reaches aMachine prog (posOf shs k) sa (posOf shs s'.reg.lpc) sb
            ∧ ACorrW rsp sb s' ∧ ∃ hl : s'.reg.lpc < body.length,
              (isCondB (body[s'.reg.lpc]'hl).li_i = true → sb.flags.zf.getD false = zf')
                ∧ CarryReq frame body s'.reg.lpc sb s' := by
        intro js hops hp' hc' hz' hcy'
        simp only [hp']
        exact ⟨_, reaches_blockP hks hblk hshk hops sa, hc', hkn, hz', hcy'⟩
      have hstepEq : stepA frame body s zf
          = fstepA frame (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss)) s zf := by
        simp only [stepA, hget]
        rw [hpc]
      rw [hstepEq] at hst
      simp only [instrOKWB] at hok
      split at hok
      · -- a width-carrying cast
        rename_i D A m w' hclK
        obtain ⟨o', hia, hm, hw⟩ := classifyK_spec hclK
        simp only [LinstrR.Lopn.injEq] at hia
        obtain ⟨rfl, rfl, rfl⟩ := hia
        simp only [castOk, Bool.and_eq_true] at hok
        rw [normA_castW hw, tagAt_castW body k hw] at hst
        have hmin : m = min (s.reg.lvm A).1 w' := by
          have hcp := hF.cast k hk
          simp only [castPosB, hbk?, Option.all_some, hclK, beq_iff_eq] at hcp
          cases hl : (narrowIn body k).lookup A with
          | none =>
            rw [hl] at hcp
            have h64 := hsafe.2.1 ii _ _ _ (by rw [hget]) A (reg_reads (by simp)) hok.2
              (by simp [carryIns]) (by
                have hsm : slotMov? (.Lopn [.reg D] o [.reg A]) = none := by
                  have ho : ¬(o = "MOVQ" ∨ o = "MOV:64") := by
                    rintro (rfl | rfl) <;> simp [castTagW] at hw
                  simp only [slotMov?, ite_eq_right ho]
                rw [hpc]
                simp only [narrowSrc, hbk?, hclK, hl, List.mem_append, not_or]
                exact ⟨by simp, not_mem_bitSrc hget hsm A⟩)
            rw [h64]
            simpa using hcp
          | some w0 =>
            rw [hl] at hcp
            have hw0 := hsafe.2.2.2 _ hget (by rw [hclK]; rfl) A w0 (by rw [hpc]; exact hl)
            rw [hw0]
            simpa using hcp
        obtain ⟨hc', -⟩ := sim_castW_bytes P rsp o D A w' m hm hok.1 hok.2 (castTagW_width hw)
          sa s zf hc hmin s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((castPieces m D A).map Prod.snd)).flags.zf.getD false
              = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          simp only [classifyA] at hcm
          split_ifs at hcm <;> simp [cmpArmB, Option.any_map] at hcm
        have hna : ∀ ii' d a s c, body[k]? ≠
            some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
          intro ii' d a s c h
          rw [hbk?] at h
          simp at h
        obtain ⟨hb, hp⟩ := castBytes P o D A m hm hok.1 hok.2
        have hops : shs[k].ops' = (castPieces m D A).map Prod.snd :=
          shapeOf_lopn_ops _ hb hp hshk
        exact hnext _ hops hpc' hc' hz' (hnoadd hna _ _)
      rename_i hclK
      by_cases h1b : bitSrc body s = []
      swap
      · -- a frame-word store of a one-bit name
        obtain ⟨S, hS1⟩ := List.exists_mem_of_ne_nil _ h1b
        obtain ⟨i, q, bS, hi, hmv, hq, hpre, hbS⟩ := bitSrc_spec hS1
        have hcq : cellParts? q = none := by simp [cellParts?, hpre]
        rw [hget] at hi
        cases hi
        obtain ⟨m, hia, hm⟩ : ∃ m, LinstrR.Lopn ds o ss = .Lopn [.reg q] m [.reg S]
            ∧ (m = "MOVQ" ∨ m = "MOV:64") := by
          unfold slotMov? at hmv
          split at hmv
          · next dst opn src heq =>
            split_ifs at hmv with hm0
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmv)
            exact ⟨_, heq, hm0⟩
          · cases hmv
        simp only [LinstrR.Lopn.injEq] at hia
        obtain ⟨rfl, rfl, rfl⟩ := hia
        by_cases hgq : gpOk q = true
        · -- a copy of a one-bit name between general-purpose names
          have hgS : gpOk S = true := hq.resolve_left (by simp [hgq])
          have hcA : classifyA (.Lopn [.reg q] o [.reg S])
              = (classify (.Lopn [.reg q] o [.reg S])).map AArm.reg := by
            rcases hm with rfl | rfl <;> simp [classifyA, isMovM, hgq, hgS]
          cases hcl : classifyA (.Lopn [.reg q] o [.reg S]) with
          | none =>
            exfalso
            rcases hm with rfl | rfl <;>
              simp (config := { decide := true }) [movImmStruct?, classifyS,
                classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX,
                classifyEI, classifyR, hcl, cellParts?_gp hgq, cellParts?_gp hgS] at hok
          | some a =>
          have hok' : a.ok P = true := by
            rcases hm with rfl | rfl <;>
              simpa (config := { decide := true }) [movImmStruct?, classifyS, classifyC,
                classifyM, classifyI, classifyL, classifyV, classifyE, classifyX, classifyEI,
                classifyR, hcl, cellParts?_gp hgq, cellParts?_gp hgS] using hok
          obtain ⟨arm, -, rfl⟩ := Option.map_eq_some_iff.mp (hcA.symm.trans hcl)
          have hai := classifyA_instr hcl
          have hli := AArm.li_eq hok'
          rw [hai] at hli
          have hli' : (AArm.reg arm).li = ((AArm.reg arm).li.fst, .reg none) := by
            rw [← hli]
            rcases hm with rfl | rfl <;> rfl
          have hmv' : slotMov? (AArm.reg arm).li.fst = some (q, S) := by
            rw [← hli]
            rcases hm with rfl | rfl <;>
              simpa (config := { decide := true }) [normA,
                LprogAsmPrinter.untagCaret_of_caret_free] using hmv
          rw [tagAt_of_not (bitMovB_of_ne (by rcases hm with rfl | rfl <;> rfl)), hli] at hst
          have hc' := AArm.simW_copy1 P rsp (.reg arm) hok' hli' hmv' hgq hgS sa s zf trivial hc
            hbS s' zf' hst
          have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          have hz' : isCondB (body[k + 1]'hkn).li_i = true →
              (aMachine.runBlock sa ((AArm.reg arm).js P)).flags.zf.getD false = zf' := by
            intro hcnd
            have hcm := hcondNext hcnd
            rw [hcl] at hcm
            simp [cmpArmB] at hcm
          have hna : ∀ ii' d a s c, body[k]? ≠
              some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
            intro ii' d a s c h
            rw [hbk?] at h
            simp only [Option.some.injEq, Linstr.mk.injEq, LinstrR.Lopn.injEq] at h
            rcases hm with rfl | rfl <;> simp at h
          have hops : shs[k].ops' = (AArm.reg arm).js P :=
            AArm.shape_ops hok' (by rw [hai]; exact hshk)
          exact hnext _ hops hpc' hc' hz' (hnoadd hna _ _)
        have hq : gpOk q = false := by simpa using hgq
        have hcl : classifyA (.Lopn [.reg q] o [.reg S]) = some (.st o q S) := by
          rcases hm with rfl | rfl <;> simp [classifyA, isMovM, hq]
        have hcS : o = "MOV:64" → cellParts? S = none := by
          rintro rfl
          cases h : cellParts? S with
          | none => rfl
          | some p => simp [slotMov?, h] at hmv
        have hok' : (AArm.st o q S).ok P = true := by
          rcases hm with rfl | rfl <;>
            simpa (config := { decide := true }) [movImmStruct?, classifyS, classifyC,
              classifyM, classifyI, classifyL, classifyV, classifyE, classifyX, classifyEI,
              classifyR, hcl, hcq, hcS]
              using hok
        have hli := AArm.li_eq hok'
        rw [tagAt_of_not (bitMovB_of_ne (by rcases hm with rfl | rfl <;> rfl))] at hst
        rw [show LinstrR.Lopn [.reg q] o [.reg S] = (AArm.st o q S).instr from rfl, hli] at hst
        have hc' := AArm.simW_st1 P rsp o q S hok' sa s zf hc hbS s' zf' hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((AArm.st o q S).js P)).flags.zf.getD false = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hcl] at hcm
          simp [cmpArmB] at hcm
        have hna : ∀ ii' d a s c, body[k]? ≠
            some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
          intro ii' d a s c h
          rw [hbk?] at h
          simp only [Option.some.injEq, Linstr.mk.injEq, LinstrR.Lopn.injEq] at h
          rcases hm with rfl | rfl <;> simp at h
        have hops : shs[k].ops' = (AArm.st o q S).js P := AArm.shape_ops hok' hshk
        exact hnext _ hops hpc' hc' hz' (hnoadd hna _ _)
      have hws : ∀ r, readsI (.Lopn ds o ss) r → gpOk r = true →
          r ∉ carryIns (.Lopn ds o ss) → (s.reg.lvm r).1 = 64 := fun r h1 h2 h3 =>
        hsafe.2.1 ii ds o ss (by rw [hget]) r h1 h2 h3 (by simp [narrowSrc, hget, hclK, h1b])
      split at hok
      · -- an untagged immediate move: a carry constant or a 32-bit constant
        rename_i D n hmv
        obtain ⟨o', hia0⟩ := movImmStruct?_spec hmv
        simp only [LinstrR.Lopn.injEq] at hia0
        obtain ⟨hds, rfl, hss⟩ := hia0
        have hia : LinstrR.Lopn ds o ss = .Lopn [.reg D] o [.imm n] := by rw [hds, hss]
        have hmi : isMovImmMnem o = true := by simpa [movImmStruct?, hds, hss] using hmv
        have hform := isMovImmMnem_iff.1 hmi
        have hnA : normA (.Lopn [.reg D] o [.imm n]) = .Lopn [.reg D] "MOV" [.imm n] := by
          rcases hform with rfl | ⟨w, hw, rfl⟩
          · simp (config := { decide := true }) [normA]
          · rw [normA_untag hw (by decide)]
            simp (config := { decide := true }) [normA]
        have htA : tagA (.Lopn [.reg D] o [.imm n]) = .reg none := by
          rcases hform with rfl | ⟨w, hw, rfl⟩
          · simp (disch := decide +kernel) [tagA, width_tag]
          · simp (disch := decide +kernel) [tagA, width_tag,
              LprogAsmPrinter.untagCaret_withWidthTag hw (m := "MOV") (by decide +kernel)]
        have henc : encodeLopn P.frame P.spillW (.Lopn [.reg D] o [.imm n]) P.qsaveB
            = encodeLopn P.frame P.spillW (.Lopn [.reg D] "MOV" [.imm n]) P.qsaveB := by
          rcases hform with rfl | ⟨w, hw, rfl⟩
          · rfl
          · exact encodeLopn_retag32 _ _ _ hw (by decide) (by decide +kernel) (by decide +kernel)
              _ _
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hc' : ACorrW rsp (aMachine.runBlock sa ((zPieces D n).map Prod.snd)) s' := by
          cases hbit : bitMovB body k (.Lopn ds o ss) with
          | true =>
            have hz : zOk D n = true := by
              have hb := hbit
              simp only [bitMovB, hmv, Bool.and_eq_true, decide_eq_true_eq] at hb
              simp only [imm32Ok, Bool.and_eq_true] at hok
              simp [zOk, hok.1, hb.1.1]
            have hli : (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss))
                = (.Lopn [.reg D] "MOV" [.imm n], MemTag.reg (some 1)) := by
              rw [tagAt, ite_eq_left hbit, hia, hnA]
            rw [hli] at hst
            exact (sim_bmov P rsp D n hz sa s zf hc s' zf' hst).1
          | false =>
            have hli : (normA (.Lopn ds o ss), tagAt body k (.Lopn ds o ss))
                = (.Lopn [.reg D] "MOV" [.imm n], MemTag.reg none) := by
              rw [tagAt_of_not hbit, hia, hnA, htA]
            rw [hli] at hst
            exact (sim_imov P rsp D n hok sa s zf hc s' zf' hst).1
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa ((zPieces D n).map Prod.snd)).flags.zf.getD false = zf' := by
          intro hcnd
          have hcm := hcondNext hcnd
          rw [hia] at hcm
          simp only [classifyA, classify] at hcm
          split at hcm <;> simp [cmpArmB] at hcm
        have hna : ∀ ii' d a s c, body[k]? ≠
            some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ := by
          intro ii' d a s c h
          rw [hbk?, hia] at h
          simp at h
        obtain ⟨hb, hp⟩ := imm32Bytes P D n hok
        have hops : shs[k].ops' = (zPieces D n).map Prod.snd :=
          shapeOf_lopn_ops _ (henc.trans hb) hp (by rw [← hia]; exact hshk)
        exact hnext _ hops hpc' hc' hz' (hnoadd hna _ _)
      rename_i hmv
      rw [tagAt_of_ne hmv] at hst
      split at hok
      · -- a slot carry arm
        rename_i c hcl
        have hia := classifyS_instr hcl
        have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) = (c.instr, MemTag.reg none) := by
          rw [← hia]
          cases c <;> simp (config := { decide := true }) [normA, tagA, SArm.instr]
        rw [hli] at hst
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
            sa'.flags.zf.getD false = zf' := by
          intro sa' hcnd
          have hcm := hcondNext hcnd
          rw [← hia] at hcm
          cases c <;> simp [SArm.instr, classifyA_three_not_cmp] at hcm
        have hops := SArm.shape_ops hok (by rw [hia]; exact hshk)
        cases c with
        | adcx D A S C =>
          have hok' := hok
          simp only [SArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨-, hAC⟩, hSC⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok'
          simp only [SArm.instr] at hia
          simp only [← hia] at hws hbk?
          have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
            hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
          have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
            hws S (reg_reads (by simp)) hS (by simp [carryIns, hSC])
          obtain ⟨hc', hzz, hcyo⟩ := sim_sadcx P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
          have hcy' : CarryReq frame body (k + 1)
              (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' := by
            intro ii' O A' S' C' hb
            have hc2 := hF.carry (k + 1) hkn
            unfold carryPrevB at hc2
            rw [hb] at hc2
            simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, hDC⟩, hsa⟩, hss⟩, -⟩ := hc2
            exact hcyo hDA hDS hDC hsa hss
          exact hnext _ hops hpc' hc' (hz' _) hcy'
        | adcxhi O A S C =>
          have hok' := hok
          simp only [SArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hAC⟩, hSC⟩, -⟩, -⟩, -⟩ := hok'
          simp only [SArm.instr] at hia
          simp only [← hia] at hws hbk?
          have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
            hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
          have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
            hws S (reg_reads (by simp)) hS (by simp [carryIns, hSC])
          have hcyk := hcy ii O A S C hbk?
          obtain ⟨hc', -, -⟩ :=
            sim_sadcxhi P rsp O A S C hok sa s zf hc hwA hwS hcyk s' zf' hst
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by
            rw [hbk?] at h
            simp at h) (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)) s'
          exact hnext _ hops hpc' hc' (hz' _) hcy'
        | adcxc D A S C =>
          obtain ⟨hCs, -, -, -, -, -⟩ := adcxc_facts hok
          simp only [SArm.instr] at hia
          simp only [← hia] at hws hbk?
          have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
            hws A (reg_reads (by simp)) hA (by simp [carryIns, ne_of_gp_slot hA hCs])
          have hwS : gpOk S = true → (s.reg.lvm S).1 = 64 := fun hS =>
            hws S (reg_reads (by simp)) hS (by simp [carryIns, ne_of_gp_slot hS hCs])
          obtain ⟨hc', hzz, hcyo⟩ := sim_sadcxc P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
          have hcy' : CarryReq frame body (k + 1)
              (aMachine.runBlock sa ((SArm.adcxc D A S C).js P)) s' := by
            intro ii' O A' S' C' hb
            have hc2 := hF.carry (k + 1) hkn
            unfold carryPrevB at hc2
            rw [hb] at hc2
            simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, -⟩, hsa⟩, hss⟩, hsc⟩ := hc2
            exact hcyo hDA hDS hsa hss hsc
          exact hnext _ hops hpc' hc' (hz' _) hcy'
      rename_i hclS
      split at hok
      · -- a carry arm
        rename_i c hcl
        have hia := classifyC_instr hcl
        cases c with
        | adcx D A S C =>
          simp only [CArm.instr] at hia
          simp only [← hia] at hst hws hshk hbk? hcondNext
          have hli : (normA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]),
              tagA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]))
              = ((CArm.adcx D A S C).instr, MemTag.reg none) := by
            simp (config := { decide := true }) [normA, tagA, CArm.instr]
          rw [hli] at hst
          have hok' := hok
          simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩, -⟩ := hok'
          have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
            (by simp [carryIns, hAC])
          have hwS : (s.reg.lvm S).1 = 64 := hws S (reg_reads (by simp)) hS
            (by simp [carryIns, hSC])
          obtain ⟨hc', hzz, hcyo⟩ := sim_adcx P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
          subst zf'
          have hpc' : s'.reg.lpc = k + 1 := by
            rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          have hz' : isCondB (body[k + 1]'hkn).li_i = true →
              (aMachine.runBlock sa (CArm.adcx D A S C).js).flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            rw [classifyA_three_not_cmp] at this
            cases this
          have hcy' : CarryReq frame body (k + 1) (aMachine.runBlock sa (CArm.adcx D A S C).js)
              s' := by
            intro ii' O A' S' C' hb
            have hc2 := hF.carry (k + 1) hkn
            unfold carryPrevB at hc2
            rw [hb] at hc2
            simp only [ite_true, Nat.add_sub_cancel, hbk?] at hc2
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, hDC⟩, -⟩, -⟩, -⟩ := hc2
            exact hcyo hDA hDS hDC
          have hops := CArm.shape_ops hok (by rw [show (CArm.adcx D A S C).instr
            = .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
          exact hnext _ hops hpc' hc' hz' hcy'
        | adcxhi O A S C =>
          simp only [CArm.instr] at hia
          simp only [← hia] at hst hws hshk hbk? hcondNext
          have hli : (normA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]),
              tagA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]))
              = ((CArm.adcxhi O A S C).instr, MemTag.reg none) := by
            simp (config := { decide := true }) [normA, tagA, CArm.instr]
          rw [hli] at hst
          have hok' := hok
          simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩ := hok'
          have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
            (by simp [carryIns, hAC])
          have hwS : (s.reg.lvm S).1 = 64 := hws S (reg_reads (by simp)) hS
            (by simp [carryIns, hSC])
          have hcyk := hcy ii O A S C hbk?
          obtain ⟨hc', hzz, hfl⟩ :=
            sim_adcxhi P rsp O A S C hok sa s zf hc hwA hwS hcyk s' zf' hst
          subst zf'
          have hpc' : s'.reg.lpc = k + 1 := by
            rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          have hz' : isCondB (body[k + 1]'hkn).li_i = true →
              (aMachine.runBlock sa (CArm.adcxhi O A S C).js).flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            rw [classifyA_three_not_cmp] at this
            cases this
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by
            rw [hbk?] at h
            simp at h) (aMachine.runBlock sa (CArm.adcxhi O A S C).js) s'
          have hops := CArm.shape_ops hok (by rw [show (CArm.adcxhi O A S C).instr
            = .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
          exact hnext _ hops hpc' hc' hz' hcy'
      · rename_i hclC
        have hnotadd : ∀ ii' d a' s'' c', body[k]? ≠
            some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a', .reg s'', .reg c']⟩ := by
          intro ii' d a' s'' c' h
          rw [hbk?] at h
          simp only [Option.some.injEq, Linstr.mk.injEq] at h
          obtain ⟨-, h2⟩ := h
          rw [h2] at hclC
          simp [classifyC] at hclC
        split at hok
        · -- a cell arm
          rename_i m hclM
          have hia := classifyM_instr hclM
          have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
              = (m.instr, MemTag.reg none) := by
            rw [← hia]
            cases m <;> simp (config := { decide := true }) [normA, tagA, MArm.instr]
          rw [hli] at hst
          have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
              sa'.flags.zf.getD false = zf' := by
            intro sa' hcnd
            have hcm := hcondNext hcnd
            rw [← hia, MArm.cmpArm_false hok] at hcm
            cases hcm
          have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          cases m with
          | ldm D n B off =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, -⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [← hia]; simp [carryIns])
            have hsafeM : ∀ p, s.reg.getW B 64 = some p →
                Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off) := fun p hp =>
              hsafe.2.2.1 ii (.Lopn [.reg D] "LOAD:64" [.reg n]) D B off p
                (by rw [hget, ← hia])
                (by simp [cellA?, hn, LprogAsmPrinter.untagCaret_of_caret_free
                  (by decide : '^' ∉ "LOAD:64".toList)]) hp
            obtain ⟨hc', -⟩ := sim_ldm P rsp D n B off hok sa s zf hc hwB hsafeM s' zf' hst
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
          | stm n B off S =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [← hia]; simp [carryIns])
            have hwS : (s.reg.lvm S).1 = 64 := hws S (by rw [← hia]; exact reg_reads (by simp))
              hS (by rw [← hia]; simp [carryIns])
            obtain ⟨hc', -⟩ := sim_stm P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
          | stv n B off S =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [← hia]; simp [carryIns])
            have hwS : (s.reg.lvm S).1 = 64 := hws S (by rw [← hia]; exact reg_reads (by simp))
              hS (by rw [← hia]; simp [carryIns])
            obtain ⟨hc', -⟩ := sim_stv P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
          | ldv D n B off =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 = 64 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [← hia]; simp [carryIns])
            have hsafeM : ∀ p, s.reg.getW B 64 = some p →
                Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off) := fun p hp =>
              hsafe.2.2.1 ii (.Lopn [.reg D] "MOV:64" [.reg n]) D B off p
                (by rw [hget, ← hia])
                (by simp [cellA?, hn, cellParts?_gp hD, LprogAsmPrinter.untagCaret_of_caret_free
                  (by decide : '^' ∉ "MOV:64".toList)]) hp
            obtain ⟨hc', -⟩ := sim_ldv P rsp D n B off hok sa s zf hc hwB hsafeM s' zf' hst
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
        · split at hok
          · -- an immediate store into a frame slot
            rename_i q v hclI
            have hia := classifyI_instr hclI
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (.Lopn [.reg q] "MOV:64" [.imm v], MemTag.reg none) := by
              rw [hia]; simp (config := { decide := true }) [normA, tagA]
            rw [hli] at hst
            obtain ⟨hc', -⟩ := sim_sti P rsp q v hok sa s zf hc s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((iPieces P q v).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              simp [classifyA, classify, cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := iBytes P q v hok
            have hops : shs[k].ops' = (iPieces P q v).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          split at hok
          · -- a wide immediate
            rename_i D v hclL
            obtain ⟨hia, -⟩ := classifyL_instr hclL
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (.Lopn [.reg D] "MOV:64" [.imm v], MemTag.reg none) := by
              rw [hia]; simp (config := { decide := true }) [normA, tagA]
            rw [hli] at hst
            obtain ⟨hc', -⟩ := sim_lmov P rsp D v hok sa s zf hc s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((lPieces D v).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              simp [classifyA, classify, cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := lBytes P D v hok
            have hops : shs[k].ops' = (lPieces D v).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          split at hok
          · -- a register select
            rename_i D C A B hclV
            have hia := classifyV_instr hclV
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], MemTag.reg none) := by
              rw [hia]; simp (config := { decide := true }) [normA, tagA]
            rw [hli] at hst
            rw [hia] at hws
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
                sa'.flags.zf.getD false = zf' := by
              intro sa' hcnd
              have hcm := hcondNext hcnd
              rw [hia, classifyA_three_not_cmp] at hcm
              cases hcm
            rcases Bool.or_eq_true_iff.mp hok with hok | hok
            · have hok' := hok
              simp only [vOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
              obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hA⟩, hB⟩, -⟩, hAC⟩, hBC⟩ := hok'
              have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
                (by simp [carryIns, hAC])
              have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
                (by simp [carryIns, hBC])
              obtain ⟨hc', -⟩ := sim_cmov P rsp D C A B hok sa s zf hc hwA hwB s' zf' hst
              obtain ⟨hb, hp⟩ := vBytes P D C A B hok
              have hops : shs[k].ops' = (vPieces D C A B).map Prod.snd :=
                shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
              exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
            rcases Bool.or_eq_true_iff.mp hok with hok | hok
            · -- a select with a slot true value
              have hok' := hok
              simp only [vtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
              obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hB⟩, -⟩, -⟩, -⟩, hBC⟩ := hok'
              have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
                (by simp [carryIns, hBC])
              obtain ⟨hc', -⟩ := sim_cmovSlot P rsp D C A B hok sa s zf hc hwB s' zf' hst
              obtain ⟨hb, hp⟩ := vtBytes P D C A B hok
              have hops : shs[k].ops' = (vtPieces P D C A B).map Prod.snd :=
                shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
              exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
            · -- a select with a slot false value
              have hok' := hok
              simp only [vfOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
              obtain ⟨⟨⟨⟨⟨⟨⟨hDg, -⟩, -⟩, -⟩, -⟩, -⟩, hAC⟩, -⟩ := hok'
              have hwA : gpOk A = true → (s.reg.lvm A).1 = 64 := fun hA =>
                hws A (reg_reads (by simp)) hA (by simp [carryIns, hAC])
              by_cases hAD : A = D
              · subst hAD
                obtain ⟨hc', -⟩ := sim_cmovSlotFE P rsp A C B hok sa s zf hc (hwA hDg) s' zf' hst
                obtain ⟨hb, hp⟩ := veBytes P A C B hok
                have hops : shs[k].ops' = (vePieces P A C B).map Prod.snd :=
                  shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
                exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
              obtain ⟨hc', -⟩ := sim_cmovSlotF P rsp D C A B hok hAD sa s zf hc hwA s' zf' hst
              obtain ⟨hb, hp⟩ := vfBytes P D C A B hok hAD
              have hops : shs[k].ops' = (vfPieces P D C A B).map Prod.snd :=
                shapeOf_lopn_ops _ hb hp (by rw [← hia]; exact hshk)
              exact hnext _ hops hpc' hc' (hz' _) (hnoadd hnotadd _ _)
          rename_i hclV
          split at hok
          · -- a materialised comparison
            rename_i n D A B hclE
            have hia := classifyE_instr hclE
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (eInstr n D A B, MemTag.reg none) := by
              rw [hia]; cases n <;> simp (config := { decide := true }) [eInstr, eMnem, normA, tagA]
            rw [hli] at hst
            rw [hia] at hws
            have hok' := hok
            simp only [eOk, Bool.and_eq_true] at hok'
            obtain ⟨⟨-, hA⟩, hB⟩ := hok'
            have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
              (by simp [eInstr, carryIns])
            have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
              (by simp [eInstr, carryIns])
            obtain ⟨hc', -⟩ := sim_sete P rsp n D A B hok sa s zf hc hwA hwB s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((ePieces n D A B).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              cases n <;> simp [eInstr, eMnem, classifyA, classify] at hcm <;>
                split_ifs at hcm <;> simp [cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := eBytes P n D A B hok
            have hops : shs[k].ops' = (ePieces n D A B).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          rename_i hclE
          split at hok
          · -- a register-count shift
            rename_i l D A B hclX
            have hia := classifyX_instr hclX
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (xInstr l D A B, MemTag.reg none) := by
              rw [hia]; cases l <;> simp (config := { decide := true }) [xInstr, xMnem, normA, tagA]
            rw [hli] at hst
            rw [hia] at hws
            have hok' := hok
            simp only [xOk, Bool.and_eq_true] at hok'
            obtain ⟨⟨-, hA⟩, hB⟩ := hok'
            have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
              (by simp [xInstr, carryIns])
            have hwB : (s.reg.lvm B).1 = 64 := hws B (reg_reads (by simp)) hB
              (by simp [xInstr, carryIns])
            obtain ⟨hc', -⟩ := sim_shrx P rsp l D A B hok sa s zf hc hwA hwB s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((xPieces l D A B).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              cases l <;> simp [xInstr, xMnem, classifyA, classify] at hcm <;>
                split_ifs at hcm <;> simp [cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := xBytes P l D A B hok
            have hops : shs[k].ops' = (xPieces l D A B).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          rename_i hclX
          split at hok
          · -- a materialised comparison with an immediate
            rename_i n D A v hclEI
            have hia := classifyEI_instr hclEI
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (eiInstr n D A v, MemTag.reg none) := by
              rw [hia]
              cases n <;> simp (config := { decide := true }) [eiInstr, eMnem, normA, tagA]
            rw [hli] at hst
            rw [hia] at hws
            have hok' := hok
            simp only [eiOk, Bool.and_eq_true] at hok'
            obtain ⟨⟨-, hA⟩, -⟩ := hok'
            have hwA : (s.reg.lvm A).1 = 64 := hws A (reg_reads (by simp)) hA
              (by simp [eiInstr, carryIns])
            obtain ⟨hc', -⟩ := sim_seteImm P rsp n D A v hok sa s zf hc hwA s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((eiPieces n D A v).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              cases n <;> simp [eiInstr, eMnem, classifyA, classify] at hcm <;>
                split_ifs at hcm <;> simp [cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := eiBytes P n D A v hok
            have hops : shs[k].ops' = (eiPieces n D A v).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          rename_i hclEI
          split at hok
          · -- an arithmetic right shift by an immediate
            rename_i D kc hclR
            have hia := classifyR_instr hclR
            have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss))
                = (rInstr D kc, MemTag.reg none) := by
              rw [hia]; simp (config := { decide := true }) [rInstr, normA, tagA]
            rw [hli] at hst
            rw [hia] at hws
            have hok' := hok
            simp only [rOk, Bool.and_eq_true] at hok'
            obtain ⟨⟨hD, -⟩, -⟩ := hok'
            have hwD : (s.reg.lvm D).1 = 64 := hws D (reg_reads (by simp)) hD
              (by simp [rInstr, carryIns])
            obtain ⟨hc', -⟩ := sim_sarImm P rsp D kc hok sa s zf hc hwD s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa ((rPieces D kc).map Prod.snd)).flags.zf.getD false
                  = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hia] at hcm
              simp [rInstr, classifyA, classify] at hcm
              split_ifs at hcm <;> simp [cmpArmB] at hcm
            obtain ⟨hb, hp⟩ := rBytes_encode P D kc hok
            have hops : shs[k].ops' = (rPieces D kc).map Prod.snd :=
              shapeOf_lopn_ops _ hb hp (by rw [hia] at hshk; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          rename_i hclR
          -- an arm of `DecodePrintedAddr`
          split at hok
          · rename_i ar hcl
            have hia := classifyA_instr hcl
            have hli := AArm.li_eq hok
            rw [← hia, hli] at hst
            have hsafeA : ar.LoadSafe rsp s := by
              cases ar with
              | ldx D B' I =>
                intro p vi hp hvi
                exact hsafe.1 ii _ D B' I (by rw [hget, ← hia]) (by simp [AArm.instr, width_tag])
                  p vi hp hvi
              | _ => trivial
            have hw : WideAt s ar.li.fst := by
              intro r hr hg
              have hfst : ar.li.fst = normA ar.instr := by rw [← hli]
              rw [hfst, readsI_normA, hia] at hr
              exact hws r hr hg (by rw [carryIns_of_classifyC hclC hclV]; simp)
            obtain ⟨hc', hzf'⟩ := AArm.simW P rsp ar hok sa s zf hc hw hsafeA s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa (ar.js P)).flags.zf.getD false = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hcl] at hcm
              exact hzf' (by simpa using hcm)
            have hops : shs[k].ops' = ar.js P := AArm.shape_ops hok (by rw [hia]; exact hshk)
            exact hnext _ hops hpc' hc' hz' (hnoadd hnotadd _ _)
          · cases hok
    | Llabel kd l =>
      have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
        unfold stepA
        rw [hget]
        simp only [hpc]
      rw [hstep] at hst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
      have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
        intro hcnd
        have := hcondNext hcnd
        simp [classifyA, cmpArmB, Option.any_map] at this
      have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
        (s.setLpc (k + 1))
      have hsk : shs[k] = .one .skip := by
        simp [shapeOf] at hshk; exact hshk.symm
      have hpos : posOf shs (k + 1) = posOf shs k := by
        rw [posOf_succ shs k hks, hsk]
        simp [nOf]
      refine ⟨sa, ?_, acorrW_setLpc hc _, hkn, hz', hcy'⟩
      change Reaches aMachine prog (posOf shs k) sa (posOf shs (k + 1)) sa
      rw [hpos]
      exact .refl _ _
    | Lcond c l =>
      cases c with
      | reg cc =>
        have hok : instrOKWB body P (.Lcond (.reg cc) l) = true :=
          hok0.resolve_left (fun h => h rfl)
        simp only [instrOKWB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
          simp [shapeOf] at hshk; exact hshk.symm
        obtain ⟨A, B, hsplit, hA⟩ := hblk
        have hj : prog[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sa.flags.zf.getD false = zf := hz rfl
        have hms := step_jcc_pol prog (posOf shs k) (posOf shs p) sa cc pol hpol hj
        rw [hzf] at hms
        by_cases hzp : zf = pol
        · have hstep : stepA frame body s zf = some (s.setLpc p, zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hp]
          rw [hstep] at hst
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
          have hz' : isCondB (body[p]'hpl).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            revert hlabp hcnd
            rcases body[p] with ⟨ii', li'⟩
            cases li' <;> simp [isCondB, isLabelB]
          have hcy' : CarryReq frame body p sa (s.setLpc p) := by
            intro ii' O A' S' C' hb
            rw [List.getElem?_eq_getElem hpl] at hb
            rw [Option.some.inj hb] at hlabp
            simp [isLabelB] at hlabp
          rw [ite_eq_left hzp] at hms
          exact ⟨sa, .single hms, acorrW_setLpc hc _, hpl, hz', hcy'⟩
        · have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hpc]
          rw [hstep] at hst
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
          have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            simp [classifyA, cmpArmB, Option.any_map] at this
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
            (s.setLpc (k + 1))
          rw [ite_eq_right hzp] at hms
          refine ⟨sa, ?_, acorrW_setLpc hc _, hkn, hz', hcy'⟩
          change Reaches aMachine prog (posOf shs k) sa (posOf shs (k + 1)) sa
          rw [posOf_succ shs k hks, hsk]
          exact .single hms
      | _ => simp [stepA, hget] at hst
    | _ => simp [stepA, hget] at hst

/-- **The run on both machines, with carry chains.** From states related by `ACorrW` at
    instruction `k` of a body in `printedAddrWB`, with the machine zero flag equal to the
    flag at a conditional branch and the machine carry flag holding the carry-out at a
    carry-out binding, every terminating run of the address machine whose indexed loads
    avoid the red-zone word and whose instructions read every general-purpose name besides a
    carry-in at width `64` is matched by a path of the machine on the decoded program from the
    index of `k` to the index of the closing return, ending in states related by `ACorrW`. Each
    step of the run is `step_simWN`. -/
theorem run_simWN {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) (rsp : BitVec 64)
    (a b : JInstr 64) :
    ∀ (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = k → (hk : k < body.length) → ACorrW rsp sa s →
      (isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf) →
      CarryReq (frameP (Params.ofBody body) rsp) body k sa s →
      runA (frameP (Params.ofBody body) rsp) body fuel s zf = some t →
      RunSafe (frameP (Params.ofBody body) rsp) body
        (SafeWN rsp body) fuel s zf →
      ∃ sa', Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
          (posOf shs k) sa (posOf shs (body.length - 1)) sa' ∧ ACorrW rsp sa' t.1 := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  set prog : List RInstr := .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])
  -- the halt at the return
  have hhalt : ∀ (fuel : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = body.length - 1 → ACorrW rsp sa s →
      runA frame body fuel s zf = some t →
      ∃ sa', Reaches aMachine prog (posOf shs (body.length - 1)) sa
          (posOf shs (body.length - 1)) sa' ∧ ACorrW rsp sa' t.1 := by
    intro fuel sa s zf t hpc hc hrun
    have hh : haltedA body s = true := by
      unfold haltedA
      rw [hpc, List.getElem?_eq_getElem (by have := hF.pos; omega)]
      have := hF.last
      revert this
      rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
      intro h
      simp only at h
      subst h
      rfl
    rw [runA_halt _ _ _ _ _ hh] at hrun
    obtain rfl := Option.some.inj hrun
    exact ⟨sa, .refl _ _, hc⟩
  intro fuel
  induction fuel with
  | zero =>
    intro k sa s zf t hpc hk hc _ _ hrun _
    by_cases hkn : k + 1 < body.length
    · simp [runA, haltedA_eq_falseW hF hpc hkn] at hrun
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt 0 sa s zf t hpc hc hrun
  | succ f ih =>
    intro k sa s zf t hpc hk hc hz hcy hrun hsafe
    by_cases hkn : k + 1 < body.length
    swap
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt (f + 1) sa s zf t hpc hc hrun
    rw [runA_step _ _ _ _ _ (haltedA_eq_falseW hF hpc hkn)] at hrun
    cases hst : stepA frame body s zf with
    | none => rw [hst] at hrun; cases hrun
    | some p =>
    obtain ⟨s', zf'⟩ := p
    rw [hst, Option.bind_some] at hrun
    obtain ⟨sb, hR, hc', hl, hz', hcy'⟩ := step_simWN hF.toCW rsp
      (fun hs => prog_split body shs a b k hs) sa s zf s' zf' hpc hk hkn hc hz hcy hsafe.1 hst
    obtain ⟨sa', hR', hC⟩ := ih s'.reg.lpc sb s' zf' t rfl hl hc' hz' hcy' hrun
      (hsafe.2 s' zf' hst)
    exact ⟨sa', hR.trans hR', hC⟩

/-- **The run on both machines, with carry chains and casts.** `run_simWN` from a run that is
    safe in the sense of `SafeW` and a start state satisfying the cast width analysis
    (`NarrowInv`), which every step of the address machine keeps (`narrowInv_step`). -/
theorem run_simW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) (rsp : BitVec 64)
    (a b : JInstr 64) (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool)
    (t : LstateA × Bool) (hpc : s.reg.lpc = k) (hk : k < body.length) (hc : ACorrW rsp sa s)
    (hz : isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf)
    (hcy : CarryReq (frameP (Params.ofBody body) rsp) body k sa s)
    (hrun : runA (frameP (Params.ofBody body) rsp) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) rsp) body (SafeW rsp body) fuel s zf)
    (hI : NarrowInv body s) :
    ∃ sa', Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
        (posOf shs k) sa (posOf shs (body.length - 1)) sa' ∧ ACorrW rsp sa' t.1 :=
  run_simWN hF rsp a b fuel k sa s zf t hpc hk hc hz hcy hrun
    (runSafe_narrow fuel s zf hI hsafe)

/-! ## 8. A covered body with carry chains against its decoded bytes -/

/-- The facts of a body in the class `printedAddrWB`. -/
theorem bodyFactsW_of {body : Lcmd} (h : printedAddrWB body = true) :
    ∃ shs, BodyFactsW body shs := by
  simp only [printedAddrWB, Bool.and_eq_true, Option.any_eq_true, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hdec, r, hlast, hret⟩, hins⟩, hcond⟩, hcar⟩, hcast⟩ := h
  have hdec' := hdec
  simp only [decodableLcmd, Bool.and_eq_true] at hdec'
  obtain ⟨shs, hs⟩ := Option.isSome_iff_exists.mp hdec'.1.1.1.1.1
  have hpos : 0 < body.length := by
    cases body with
    | nil => simp at hlast
    | cons _ _ => simp
  refine ⟨shs, ⟨hs, hpos, ?_, fun k hk => ?_, fun k hk => hcond k hk, fun k hk => hcar k hk,
    fun k hk => hcast k hk⟩⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    obtain rfl := Option.some.inj hlast
    revert hret
    unfold isRetB
    split <;> simp_all
  · have hm : (body[k]'(by omega)) ∈ body.dropLast := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    exact hins _ hm

/-- The branch targets of a covered body resolve to the decoded index of their label. -/
theorem targetsOK_ofW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) :
    TargetsOK body shs (fundefItemsL body shs) := by
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  intro sh hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hshk := hsh k (by omega) hk
  refine ⟨fun l hs => ?_, fun l ht => ?_⟩
  · rw [hs] at hshk
    obtain ⟨ra, f, he, -⟩ := eq_of_shapeOf_callSym hshk
    by_cases hkn : k + 1 < body.length
    · have hok := hF.instr k hkn
      rw [he] at hok
      simp [instrOKWB] at hok
    · have hlast := hF.last
      have hk' : k = body.length - 1 := by omega
      subst hk'
      rw [hlast] at he
      cases he
  by_cases hkn : k + 1 < body.length
  · have hok := hF.instr k hkn
    revert hshk hok
    rcases body[k] with ⟨ii, li⟩
    cases li with
    | Lcond c l' =>
      cases c with
      | reg cc =>
        simp only [shapeOf, Option.some.injEq, instrOKWB, Bool.and_eq_true,
          Option.isSome_iff_exists]
        intro hsk hok
        rw [← hsk] at ht
        simp only [shTarget, Shape.target, Option.some.injEq] at ht
        subst ht
        obtain ⟨-, p, hp⟩ := hok
        obtain ⟨off, ho⟩ := labelPos_fundef hF.shapes hp
        exact ⟨off, by rw [hp]; exact ho⟩
      | _ => simp [instrOKWB]
    | Lopn ds o ss =>
      intro hsk _
      rcases shapeOfBytes_ok (bs := encodeLopn _ _ (.Lopn ds o ss) _) hsk with
        ⟨q, he, -, -⟩ | ⟨pcs, he, -, -⟩ <;> rw [he] at ht <;> simp [shTarget, Shape.target] at ht
    | Llabel kd l' =>
      intro hsk _
      simp only [shapeOf, Option.some.injEq] at hsk
      rw [← hsk] at ht
      simp [shTarget, Shape.target] at ht
    | _ => simp [instrOKWB]
  · have hk' : k = body.length - 1 := by omega
    subst hk'
    have hlast := hF.last
    revert hshk hlast
    rcases body[body.length - 1]'(by omega) with ⟨ii, li⟩
    intro hshk hlast
    simp only at hlast hshk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hshk
    rw [← hshk] at ht
    simp [shTarget, Shape.target] at ht

/-- **The decoded bytes of a covered printed body with carry chains simulate its run on the
    address machine.** For every body in the class `printedAddrWB`, from a machine state `sa`
    and an address state `s` at program counter `0` that `ACorrW` relates at the entry stack
    register with equal memories, every terminating run of the address machine on the body,
    with frame words at their addresses below the entry stack register, whose indexed loads
    read outside the red-zone word and whose instructions read every general-purpose name
    besides a carry-in at width `64`, is matched by a halting run of the machine on the decoded
    function bytes. At the end the stack register is restored, every general-purpose name holds
    the value of its machine register, a bit the machine register zero-extends or a 32- or
    16-bit cell of it (`NarrowCell`), and the memories agree outside
    the red-zone word. The halting run makes no call. -/
theorem printedAddr_simW_noCall (body : Lcmd) (h : printedAddrWB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R))
      ∨ ∃ b : BitVec 1, s.reg.lvm R = ⟨1, b⟩ ∧ sa.regs (phys R) = b.setWidth 64)
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool)
    (hrun : runA (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (SafeW (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ HaltsNoCall aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ R, gpOk R = true → t.1.reg.getW R 64 = some (sa'.regs (phys R))
          ∨ (∃ b : BitVec 1, t.1.reg.lvm R = ⟨1, b⟩ ∧ sa'.regs (phys R) = b.setWidth 64)
          ∨ NarrowCell (t.1.reg.lvm R) (sa'.regs (phys R)))
      ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → t.1.mem x = sa'.mem x) := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrWB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  set P := Params.ofBody body
  set F := P.frame
  set rsp := frameRsp body sa with hrsp
  set prog : List RInstr := .op (leaFrame (-(Int.ofNat F)))
    :: (shs.flatMap (blkOf body shs) ++ [.op (leaFrame (Int.ofNat F)), .ret]) with hprog
  have hdecode : decodeLprog (encodeLfundefBytes body) = some prog := by
    refine decodeLprog_encodeLfundefBytes hdec ?_
    rw [fundefLayout, fundefItems,
      show shapesD P body = shs by
        rw [shapesD, show shapesOf P body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_ofW hF)
  -- the prologue
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  have hc0 : ACorrW rsp sa1 s :=
    { regs := fun R hR => by
        rw [hl1, ite_eq_right (fun e => (gpFacts hR).physNe e)]
        exact (hent R hR).elim Or.inl fun hb => Or.inr (Or.inl hb)
      sp := by rw [hl1, ite_eq_left rfl, hrsp]; rfl
      mem := fun x _ => by rw [hmem, hm1] }
  have hz0 : isCondB (body[0]'hF.pos).li_i = true → sa1.flags.zf.getD false = zf := by
    intro hcnd
    have hc := hF.cond 0 hF.pos
    revert hc hcnd
    unfold condPrevB
    rw [List.getElem?_eq_getElem hF.pos]
    rcases body[0]'hF.pos with ⟨ii, li⟩
    cases li <;> simp [isCondB]
  have hcy0 : CarryReq (frameP P rsp) body 0 sa1 s := by
    intro ii O A S C hb
    have hc := hF.carry 0 hF.pos
    unfold carryPrevB at hc
    rw [hb] at hc
    simp at hc
  obtain ⟨sa2, hR, hc2⟩ :=
    run_simW hF rsp _ _ fuel 0 sa1 s zf t hpc hF.pos hc0 hz0 hcy0 hrun hsafe
      (fun i _ _ r w hl => by rw [hpc, narrowIn_zero] at hl; cases hl)
  -- the epilogue
  have hskip : shs[shs.length - 1]'(by have := hF.pos; omega) = .one .skip := by
    have hsk := hsh (body.length - 1) (by have := hF.pos; omega) (by have := hF.pos; omega)
    have hlast := hF.last
    revert hsk hlast
    rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
    intro hsk hlast
    simp only at hlast hsk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hsk
    simp only [hl] at hsk ⊢
    exact hsk.symm
  obtain ⟨he1, he2⟩ := prog_end body shs (leaFrame (-(Int.ofNat F))) (leaFrame (Int.ofNat F))
    (by have := hF.pos; omega) hskip
  rw [hl] at he1 he2
  obtain ⟨hl2, hm2⟩ := evalInstrA_leaFrame sa2 (Int.ofNat F)
  refine ⟨prog, evalInstrA sa2 (leaFrame (Int.ofNat F)), hdecode,
    ⟨posOf shs (body.length - 1) + 1, ?_, he2⟩, ?_, fun R hR => ?_, fun x hx => ?_⟩
  · have h01 : Reaches aMachine prog 0 sa 1 sa1 := .single (aMachine_step_op prog 0 sa _ rfl)
    have hpos0 : posOf shs 0 = 1 := by simp [posOf]
    rw [hpos0] at hR
    exact (h01.trans hR).trans (.single (aMachine_step_op prog _ sa2 _ he1))
  · rw [hl2, ite_eq_left rfl, hc2.sp, hrsp, frameRsp]
    simp [F, P, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · rw [hl2, ite_eq_right (fun e => (gpFacts hR).physNe e)]
    exact hc2.regs R hR
  · rw [hm2]
    exact hc2.mem x hx

/-- **The decoded bytes of a body in `printedAddrWB` simulate its runs.** The statement of
    `printedAddr_simW_noCall` with the halting run as a halting run through calls
    (`halts_of_haltsNoCall`). -/
theorem printedAddr_simW (body : Lcmd) (h : printedAddrWB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R))
      ∨ ∃ b : BitVec 1, s.reg.lvm R = ⟨1, b⟩ ∧ sa.regs (phys R) = b.setWidth 64)
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool)
    (hrun : runA (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (SafeW (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ R, gpOk R = true → t.1.reg.getW R 64 = some (sa'.regs (phys R))
          ∨ (∃ b : BitVec 1, t.1.reg.lvm R = ⟨1, b⟩ ∧ sa'.regs (phys R) = b.setWidth 64)
          ∨ NarrowCell (t.1.reg.lvm R) (sa'.regs (phys R)))
      ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → t.1.mem x = sa'.mem x) := by
  obtain ⟨prog, sa', hd, hh, h1, h2, h3⟩ :=
    printedAddr_simW_noCall body h sa s zf hpc hent hmem fuel t hrun hsafe
  exact ⟨prog, sa', hd, halts_of_haltsNoCall hh, h1, h2, h3⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
