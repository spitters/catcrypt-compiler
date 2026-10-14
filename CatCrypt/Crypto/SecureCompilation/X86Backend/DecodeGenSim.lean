/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop

@[expose] public section

set_option autoImplicit false

/-!
# Checked decoded-instruction simulations

`DecodedLsemStep` proves one `DecSim` lemma per instruction class: a flag-machine instruction
against the machine instructions it decodes to, under the correspondence `DecLsemCorr`. This
module turns the register classes into a Boolean check `stepOK` on an instruction and its
machine instructions, proves the check sound class by class, and composes the checks over a
body by one induction and over a guarded counted loop node.

## The correspondence

The live set is a list of names `N` on which the register map `π` is injective
(`InjOn`, checked by `injB`). Every write to a name of `N` then keeps `N` live
(`survives_of_injOn`), so one relation `GCorr π N Lay frame K zl` holds before and after
every instruction; only the zero-flag component `zl` changes.

## The classes

`stepOK π N i js` accepts, for names of `N`:

* the register copy `MOV:64 d, a` and the count-`0` shift `SHL:0:64 d, a` against
  `mov %a, %d`, or against nothing when `d` and `a` share a register;
* `SHR:k:64 d, a` with `0 < k < 64` against `shr $k, %d`, `d` and `a` in one register;
* the shifts with the count as an immediate operand (`shiftOK`, the form `shiftLinstr` emits):
  `SHL:64 d, a, #0` as the copy, and `SHR:64`/`SHL:64 d, a, #k` with `0 < k < 64` against the
  machine shift in place or after `mov %a, %d`;
* the immediate move `MOV:64 d, #n` against `mov $n, %d`;
* the two-address operations `ADD`, `SUB`, `AND`, `XOR`, `OR`, `MUL` at width `64`, register
  and (`ADD`, `SUB`) immediate second source, against the machine operation on the register of
  `d`, which is the register of `a`;
* the flag compares `CMP:64 c, r` and `CMP:64 c, #k`.

The loads and stores through a pointer reloaded from a frame slot and the high half of the
widening multiply carry machine-state side conditions and are not in the check.

## Main results

* `shiftImmS`, `fstepF_shiftImmS`, `shiftOK`, `shift_sound`: the immediate-operand shifts.
* `decSim_of_stepOK`: an accepted instruction simulates its machine instructions.
* `decSim_of_bodyOK`: a body accepted instruction by instruction simulates the concatenation
  of its machine instructions.
* `decNode_halts_gen`: `DecodedLsemLoop.decNode_halts` at a node whose seeds and loop body are
  accepted and whose decoded loop body writes the counter register once, by `sub $1`: the
  machine halts on `nodeLayout`, the flag machine halts, and the exit states are related by
  `GCorr` before the machine epilogue.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop XLoop.cmpInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop

/-! ## 1. The correspondence on a fixed live set -/

/-- The correspondence `DecLsemCorr` with the names of `N` live. -/
abbrev GCorr (π : String → String) (N : List String) (Lay : Layout)
    (frame : String → Option (BitVec 64)) (K : String → Nat → Prop) (zl : Prop) :
    AState → LstateM → Bool → Prop :=
  DecLsemCorr π (· ∈ N) Lay frame K zl

/-- `π` is injective on `N`. -/
def InjOn (π : String → String) (N : List String) : Prop :=
  ∀ r ∈ N, ∀ s ∈ N, π r = π s → r = s

/-- The injectivity of `π` on `N`, as a Boolean. -/
def injB (π : String → String) (N : List String) : Bool :=
  N.all (fun r => N.all (fun s => π r != π s || r == s))

theorem injOn_of_injB {π : String → String} {N : List String} (h : injB π N = true) :
    InjOn π N := by
  intro r hr s hs he
  simp only [injB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact (h r hr s hs).resolve_left (not_not.mpr he)

theorem survives_of_injOn {π : String → String} {N : List String} (hinj : InjOn π N)
    {d : String} (hd : d ∈ N) : Survives π (· ∈ N) (· ∈ N) d := fun r hr =>
  if h : r = d then Or.inl h else Or.inr ⟨hr, fun he => h (hinj r hr d hd he)⟩

variable {π : String → String} {N : List String} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop}

/-- The correspondence without the zero flag. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.DecLsemCorr.dropZf
    {L : String → Prop} {zl : Prop} {sa : AState} {b : LstateM}
    {zf : Bool} (h : DecLsemCorr π L Lay frame K zl sa b zf) :
    DecLsemCorr π L Lay frame K False sa b zf where
  regs := h.regs
  zfEq := fun hz => hz.elim
  cells := h.cells
  slots := h.slots

/-- A simulation whose target drops the zero flag. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.DecSim.dropZf
    {zl zl' : Prop} {ls : List LinstrRM} {js : List (JInstr 64)}
    (h : DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K zl') ls js) :
    DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K False) ls js :=
  h.weaken (fun _ _ _ h => h) (fun _ _ _ h => h.dropZf)

/-- A simulation carries a property of the machine state that the machine block
    establishes. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.DecSim.andMach
    {I J : AState → LstateM → Bool → Prop} {P Q : AState → Prop}
    {ls : List LinstrRM} {js : List (JInstr 64)} (h : DecSim I J ls js)
    (hm : ∀ sa, P sa → Q (aMachine.runBlock sa js)) :
    DecSim (fun sa b zf => I sa b zf ∧ P sa) (fun sa b zf => J sa b zf ∧ Q sa) ls js := by
  intro sa b zf hi
  obtain ⟨b', z', hr, hj⟩ := h sa b zf hi.1
  exact ⟨b', z', hr, hj, hm sa hi.2⟩

/-! ### Shifts with the count as an immediate operand -/

/-- The immediate shift `m:64 d, a, #k` with the count as a second, immediate operand: the form
    `JasminLsemShift.shiftLinstr` emits. -/
def shiftImmS (m d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 m) [.reg a, .imm k], .reg none)

/-- The flag machine steps the immediate-operand shift as the count-in-mnemonic shift. -/
theorem fstepF_shiftImmS {m : String} (hm : m = "SHR" ∨ m = "SHL") (d a : String) (k : Nat)
    (b : LstateM) (zf : Bool) :
    fstepF (shiftImmS m d a k) b zf = fstepF (immShiftI m d a k) b zf := by
  have hm' : m = "SHR" ∨ m = "SHL" ∨ m = "SAR" := by
    rcases hm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rw [shiftImmS, immShiftI, JasminLsemExportTransfer.fstepF_immShiftStruct hm' 64 k d a,
    JasminLsemExportTransfer.fstepF_immShiftWire m hm' 64 k d a b zf,
    JasminLsemExportTransfer.lsemStepN_immShiftCount hm' 64 k d a (Or.inl rfl) b.reg]

open JasminLsemShift in
theorem fstepF_shlImmI (d a : String) (k : Nat) (hk : k < 64) (b : LstateM) (zf : Bool)
    (va : BitVec 64) (hva : b.reg.getW a 64 = some va) :
    fstepF (immShiftI "SHL" d a k) b zf = some ((b.setReg d (va <<< k)).nextPc, zf) := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [immShiftI, JasminLsemExportTransfer.fstepF_immShiftWire "SHL" (Or.inr (Or.inl rfl)) 64 k
      d a b zf,
    JasminLsemExportTransfer.lsemStepN_immShiftCount (Or.inr (Or.inl rfl)) 64 k d a (Or.inl rfl)
      b.reg,
    lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SHL]; decide))]
  simp only [lsemStepN, readReg_of_getW hva, evalOperandN, stripWidthTag_withWidthTag_SHL,
    applyOpnN, Option.map_some, hkn, shiftMask_of_lt hk]
  rfl

/-- The data word of `shl $k` for a count `0 < k < 64`. -/
theorem x86_SHL_word_imm (v : BitVec 64) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) :
    (x86_SHL v (BitVec.ofNat 64 k)).word = v <<< k := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [x86_SHL, shiftCount, hkn, shiftMask_of_lt hk, if_neg hk0, rflags_OF, wshl,
    Nat.min_eq_right hk.le]

/-- **The immediate-operand shifts.** `SHL:64 d, a, #0` against `mov %a, %d` or, with `d` and
    `a` in one register, nothing; `SHR:64`/`SHL:64 d, a, #k` with `0 < k < 64` against the
    machine shift in place, or against `mov %a, %d` and the machine shift. -/
def shiftOK (π : String → String) (d opn a : String) (k : Nat) (js : List (JInstr 64)) :
    Bool :=
  (opn == withWidthTag 64 "SHL" && k == 0
      && (js == [.mov (π d) (.reg (π a))] || (π d == π a && js.isEmpty)))
  || (k != 0 && decide (k < 64)
      && ((opn == withWidthTag 64 "SHR"
            && ((π d == π a && js == [.shr (π d) (.imm k)])
              || js == [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)]))
        || (opn == withWidthTag 64 "SHL"
            && ((π d == π a && js == [.shl (π d) (.imm k)])
              || js == [.mov (π d) (.reg (π a)), .shl (π d) (.imm k)]))))

section ShiftImmS

variable {L L' : String → Prop} {zl : Prop}

/-- `SHR:64 d, a, #k` against `shr $k, %d` with `d` and `a` in one register, `0 < k < 64`. -/
theorem decSim_shrImmS (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [shiftImmS "SHR" d a k] [.shr (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, (fstepF_shiftImmS (Or.inl rfl) d a k b zf).trans
        (fstepF_shrImmI d a k hk b zf _ (h.regs a ha)),
      h.write d _ _ (fun r => by
        show (if r = π d then (x86_SHR (sa.regs (π d)) (BitVec.ofNat 64 k)).word
          else sa.regs r) = _
        rw [x86_SHR_word_imm _ k hk0 hk, hda]) rfl hL (fun hz => hz.elim)⟩

/-- `SHL:64 d, a, #k` against `shl $k, %d` with `d` and `a` in one register, `0 < k < 64`. -/
theorem decSim_shlImmS (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [shiftImmS "SHL" d a k] [.shl (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, (fstepF_shiftImmS (Or.inr rfl) d a k b zf).trans
        (fstepF_shlImmI d a k hk b zf _ (h.regs a ha)),
      h.write d _ _ (fun r => by
        show (if r = π d then (x86_SHL (sa.regs (π d)) (BitVec.ofNat 64 k)).word
          else sa.regs r) = _
        rw [x86_SHL_word_imm _ k hk0 hk, hda]) rfl hL (fun hz => hz.elim)⟩

/-- `SHR:64 d, a, #k` against `mov %a, %d` and `shr $k, %d`, `0 < k < 64`. -/
theorem decSim_shrImmS_mov (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [shiftImmS "SHR" d a k] [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)] := by
  intro sa b zf h
  refine ⟨_, zf, ?_, h.write d (sa.regs (π a) >>> k)
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)]) (fun r => ?_) rfl hL
    (fun hz => hz.elim)⟩
  · rw [runStraightF_singleton, fstepF_shiftImmS (Or.inl rfl) d a k b zf,
      fstepF_shrImmI d a k hk b zf _ (h.regs a ha)]
  · show (if r = π d then (x86_SHR (if π d = π d then sa.regs (π a) else sa.regs (π d))
        (BitVec.ofNat 64 k)).word else (if r = π d then sa.regs (π a) else sa.regs r)) = _
    rw [if_pos rfl, x86_SHR_word_imm _ k hk0 hk]
    split <;> simp_all

/-- `SHL:64 d, a, #k` against `mov %a, %d` and `shl $k, %d`, `0 < k < 64`. -/
theorem decSim_shlImmS_mov (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [shiftImmS "SHL" d a k] [.mov (π d) (.reg (π a)), .shl (π d) (.imm k)] := by
  intro sa b zf h
  refine ⟨_, zf, ?_, h.write d (sa.regs (π a) <<< k)
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), .shl (π d) (.imm k)]) (fun r => ?_) rfl hL
    (fun hz => hz.elim)⟩
  · rw [runStraightF_singleton, fstepF_shiftImmS (Or.inr rfl) d a k b zf,
      fstepF_shlImmI d a k hk b zf _ (h.regs a ha)]
  · show (if r = π d then (x86_SHL (if π d = π d then sa.regs (π a) else sa.regs (π d))
        (BitVec.ofNat 64 k)).word else (if r = π d then sa.regs (π a) else sa.regs r)) = _
    rw [if_pos rfl, x86_SHL_word_imm _ k hk0 hk]
    split <;> simp_all

/-- The count-`0` shift `SHL:64 d, a, #0` against the copy `mov %a, %d`. -/
theorem decSim_shl0S (d a : String) (ha : L a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [shiftImmS "SHL" d a 0] [.mov (π d) (.reg (π a))] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, (fstepF_shiftImmS (Or.inr rfl) d a 0 b zf).trans
        (fstepF_shl0I d a b zf _ (h.regs a ha)),
      h.write d _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)⟩

/-- The count-`0` shift `SHL:64 d, a, #0` with `d` and `a` in one register needs no machine
    instruction. -/
theorem decSim_shl0S_elided (d a : String) (ha : L a) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [shiftImmS "SHL" d a 0] [] :=
  DecSim.lsemOnly fun sa b zf h =>
    ⟨_, zf, (fstepF_shiftImmS (Or.inr rfl) d a 0 b zf).trans
        (fstepF_shl0I d a b zf _ (h.regs a ha)),
      h.write d _ sa (fun r => by split <;> simp_all) rfl hL (fun hz => h.zfEq hz)⟩

/-- **The immediate-operand shifts simulate their machine instructions.** -/
theorem shift_sound {d opn a : String} {k : Nat} {js : List (JInstr 64)} (ha : L a)
    (hS : Survives π L L' d) (h : shiftOK π d opn a k js = true) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [(.Lopn [.reg d] opn [.reg a, .imm k], .reg none)] js := by
  have dz : ∀ {ls : List LinstrRM} {ms : List (JInstr 64)},
      DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl) ls ms →
      DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False) ls ms :=
    fun h => h.weaken (fun _ _ _ h => h) (fun _ _ _ h => h.dropZf)
  simp only [shiftOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.isEmpty_iff] at h
  rcases h with ⟨⟨rfl, rfl⟩, hjs⟩ | ⟨⟨hk0, hk⟩, ⟨rfl, hjs⟩ | ⟨rfl, hjs⟩⟩
  · rcases hjs with rfl | ⟨hda, rfl⟩
    · exact dz (decSim_shl0S d a ha hS)
    · exact dz (decSim_shl0S_elided d a ha hda hS)
  · rcases hjs with ⟨hda, rfl⟩ | rfl
    · exact decSim_shrImmS d a k hk0 hk ha hda hS
    · exact decSim_shrImmS_mov d a k hk0 hk ha hS
  · rcases hjs with ⟨hda, rfl⟩ | rfl
    · exact decSim_shlImmS d a k hk0 hk ha hda hS
    · exact decSim_shlImmS_mov d a k hk0 hk ha hS

/-- `SHL:k:64 d, a` against `shl $k, %d` with `d` and `a` in one register, `0 < k < 64`. -/
theorem decSim_shlImmI (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [immShiftI "SHL" d a k] [.shl (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_shlImmI d a k hk b zf _ (h.regs a ha),
      h.write d _ _ (fun r => by
        show (if r = π d then (x86_SHL (sa.regs (π d)) (BitVec.ofNat 64 k)).word
          else sa.regs r) = _
        rw [x86_SHL_word_imm _ k hk0 hk, hda]) rfl hL (fun hz => hz.elim)⟩

/-- `SHR:k:64 d, a` against `mov %a, %d` and `shr $k, %d`, `0 < k < 64`. -/
theorem decSim_shrImmI_mov (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [immShiftI "SHR" d a k] [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)] := by
  intro sa b zf h
  refine ⟨_, zf, ?_, h.write d (sa.regs (π a) >>> k)
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), .shr (π d) (.imm k)]) (fun r => ?_) rfl hL
    (fun hz => hz.elim)⟩
  · rw [runStraightF_singleton, fstepF_shrImmI d a k hk b zf _ (h.regs a ha)]
  · show (if r = π d then (x86_SHR (if π d = π d then sa.regs (π a) else sa.regs (π d))
        (BitVec.ofNat 64 k)).word else (if r = π d then sa.regs (π a) else sa.regs r)) = _
    rw [if_pos rfl, x86_SHR_word_imm _ k hk0 hk]
    split <;> simp_all

/-- `SHL:k:64 d, a` against `mov %a, %d` and `shl $k, %d`, `0 < k < 64`. -/
theorem decSim_shlImmI_mov (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [immShiftI "SHL" d a k] [.mov (π d) (.reg (π a)), .shl (π d) (.imm k)] := by
  intro sa b zf h
  refine ⟨_, zf, ?_, h.write d (sa.regs (π a) <<< k)
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), .shl (π d) (.imm k)]) (fun r => ?_) rfl hL
    (fun hz => hz.elim)⟩
  · rw [runStraightF_singleton, fstepF_shlImmI d a k hk b zf _ (h.regs a ha)]
  · show (if r = π d then (x86_SHL (if π d = π d then sa.regs (π a) else sa.regs (π d))
        (BitVec.ofNat 64 k)).word else (if r = π d then sa.regs (π a) else sa.regs r)) = _
    rw [if_pos rfl, x86_SHL_word_imm _ k hk0 hk]
    split <;> simp_all

end ShiftImmS

/-! ## 2. The check on one instruction -/

/-- The one-source register forms: the copy and the count-`0` shift against `mov` or
    nothing, and the right and left shifts by a count in `(0, 64)` against the machine shift
    in place or against `mov` and the machine shift. -/
def unaryOK (π : String → String) (d opn a : String) (js : List (JInstr 64)) : Bool :=
  ((opn == withWidthTag 64 "MOV" || opn == withWidthTag 64 ("SHL" ++ ":" ++ toString 0))
      && (js == [.mov (π d) (.reg (π a))] || (π d == π a && js.isEmpty)))
  || (match js with
      | [.shr D (.imm k)] => opn == withWidthTag 64 ("SHR" ++ ":" ++ toString k)
          && k != 0 && decide (k < 64) && D == π d && π d == π a
      | [.shl D (.imm k)] => opn == withWidthTag 64 ("SHL" ++ ":" ++ toString k)
          && k != 0 && decide (k < 64) && D == π d && π d == π a
      | [.mov D (.reg A), .shr D' (.imm k)] =>
          opn == withWidthTag 64 ("SHR" ++ ":" ++ toString k)
          && k != 0 && decide (k < 64) && D == π d && A == π a && D' == π d
      | [.mov D (.reg A), .shl D' (.imm k)] =>
          opn == withWidthTag 64 ("SHL" ++ ":" ++ toString k)
          && k != 0 && decide (k < 64) && D == π d && A == π a && D' == π d
      | _ => false)

/-- The two-source register forms: the flag compare, and the two-address operations with the
    destination in the register of the first source. -/
def binOK (π : String → String) (d opn a c : String) (js : List (JInstr 64)) : Bool :=
  (opn == withWidthTag 64 "CMP" && d == a && js == [.cmp (π a) (.reg (π c))])
  || (π d == π a &&
      ((opn == "ADD:64" && js == [.add (π d) (.reg (π c))])
      || (opn == "SUB:64" && js == [.sub (π d) (.reg (π c))])
      || (opn == "AND:64" && js == [.and_ (π d) (.reg (π c))])
      || (opn == "XOR:64" && js == [.xor_ (π d) (.reg (π c))])
      || (opn == "OR:64" && js == [.or_ (π d) (.reg (π c))])
      || (opn == "MUL:64" && js == [.imul (π d) (.reg (π c))])))

/-- The register-immediate forms: the flag compare, and `ADD`/`SUB` with the destination in
    the register of the first source. -/
def immOK (π : String → String) (d opn a : String) (k : Nat) (js : List (JInstr 64)) :
    Bool :=
  (opn == withWidthTag 64 "CMP" && d == a && js == [.cmp (π a) (.imm k)])
  || (π d == π a &&
      ((opn == "ADD:64" && js == [.add (π d) (.imm k)])
      || (opn == "SUB:64" && js == [.sub (π d) (.imm k)])))

/-- **The check.** A flag-machine instruction of a register class over names of `N`,
    against the machine instructions of that class. -/
def stepOK (π : String → String) (N : List String) (i : LinstrRM) (js : List (JInstr 64)) :
    Bool :=
  match i with
  | (.Lopn [.reg d] opn [.reg a], .reg none) =>
      N.contains d && N.contains a && unaryOK π d opn a js
  | (.Lopn [.reg d] opn [.imm n], .reg none) =>
      N.contains d && opn == withWidthTag 64 "MOV" && js == [.mov (π d) (.imm n)]
  | (.Lopn [.reg d] opn [.reg a, .reg c], .reg none) =>
      N.contains d && N.contains a && N.contains c && binOK π d opn a c js
  | (.Lopn [.reg d] opn [.reg a, .imm k], .reg none) =>
      N.contains d && N.contains a && (immOK π d opn a k js || shiftOK π d opn a k js)
  | _ => false

/-- The flag compare, as a Boolean: the instructions after which the zero flag is tracked. -/
def isCmpB (i : LinstrRM) : Bool :=
  match i with
  | (.Lopn [.reg _] opn [.reg _, _], .reg none) => opn == withWidthTag 64 "CMP"
  | _ => false

theorem withWidthTag_MOV : withWidthTag 64 "MOV" = "MOV:64" := rfl
theorem withWidthTag_CMP : withWidthTag 64 "CMP" = "CMP:64" := rfl

theorem unary_sound (hinj : InjOn π N) {d opn a : String} {js : List (JInstr 64)}
    (hd : d ∈ N) (ha : a ∈ N) (h : unaryOK π d opn a js = true) {zl : Prop} :
    DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K False)
      [(.Lopn [.reg d] opn [.reg a], .reg none)] js := by
  have hS := survives_of_injOn hinj hd
  simp only [unaryOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hopn, hjs⟩ | h
  · rcases hopn with rfl | rfl
    · rcases hjs with rfl | ⟨hda, hjs⟩
      · exact (decSim_movReg (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a ha hS).dropZf
      · have : js = [] := by simpa using hjs
        subst this
        exact (decSim_movReg_elided (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a ha
          hda hS).dropZf
    · rcases hjs with rfl | ⟨hda, hjs⟩
      · exact (decSim_shl0 (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a ha hS).dropZf
      · have : js = [] := by simpa using hjs
        subst this
        exact (decSim_shl0_elided (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a ha
          hda hS).dropZf
  · split at h
    · rename_i D k
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hk0⟩, hk⟩, rfl⟩, hda⟩ := h
      exact decSim_shrImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k hk0 hk ha
        hda hS
    · rename_i D k
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hk0⟩, hk⟩, rfl⟩, hda⟩ := h
      exact decSim_shlImmI (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k hk0 hk ha
        hda hS
    · rename_i D A D' k
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨rfl, hk0⟩, hk⟩, rfl⟩, rfl⟩, rfl⟩ := h
      exact decSim_shrImmI_mov (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k hk0 hk
        ha hS
    · rename_i D A D' k
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨rfl, hk0⟩, hk⟩, rfl⟩, rfl⟩, rfl⟩ := h
      exact decSim_shlImmI_mov (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k hk0 hk
        ha hS
    · exact absurd h (by simp)

theorem bin_sound (hinj : InjOn π N) {d opn a c : String} {js : List (JInstr 64)}
    (hd : d ∈ N) (ha : a ∈ N) (hc : c ∈ N) (h : binOK π d opn a c js = true) {zl : Prop} :
    DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K
      (isCmpB (.Lopn [.reg d] opn [.reg a, .reg c], .reg none) = true))
      [(.Lopn [.reg d] opn [.reg a, .reg c], .reg none)] js := by
  have hS := survives_of_injOn hinj hd
  simp only [binOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨hda, h⟩
  · have hcmp : isCmpB (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, .reg c], .reg none)
        = true := by simp [isCmpB]
    rw [hcmp]
    exact (decSim_cmpReg (Lay := Lay) (frame := frame) (K := K) (zl := zl) d c ha hc).weaken
      (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
  · have hnc : ∀ o, o ≠ withWidthTag 64 "CMP" →
        isCmpB (.Lopn [.reg d] o [.reg a, .reg c], .reg none) = false := fun o ho => by
      simp [isCmpB, ho]
    rcases h with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      | ⟨rfl, rfl⟩)
    · rw [hnc _ (by decide)]
      exact (decSim_add (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_sub (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_and (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_xor (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_or (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_imul (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a c ha hc hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)

theorem imm_sound (hinj : InjOn π N) {d opn a : String} {k : Nat} {js : List (JInstr 64)}
    (hd : d ∈ N) (ha : a ∈ N) (h : immOK π d opn a k js = true) {zl : Prop} :
    DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K
      (isCmpB (.Lopn [.reg d] opn [.reg a, .imm k], .reg none) = true))
      [(.Lopn [.reg d] opn [.reg a, .imm k], .reg none)] js := by
  have hS := survives_of_injOn hinj hd
  simp only [immOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨hda, h⟩
  · have hcmp : isCmpB (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, .imm k], .reg none)
        = true := by simp [isCmpB]
    rw [hcmp]
    exact (decSim_cmpImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d k ha).weaken
      (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
  · have hnc : ∀ o, o ≠ withWidthTag 64 "CMP" →
        isCmpB (.Lopn [.reg d] o [.reg a, .imm k], .reg none) = false := fun o ho => by
      simp [isCmpB, ho]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hnc _ (by decide)]
      exact (decSim_addImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k ha hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)
    · rw [hnc _ (by decide)]
      exact (decSim_subImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d a k ha hda
        hS).weaken (fun _ _ _ h => h) (fun _ _ _ h => by simpa using h)

/-- **An accepted instruction simulates its machine instructions.** From the correspondence
    on `N`, the flag machine's step succeeds and the machine block ends in the
    correspondence on `N`, with the zero flag tracked after a compare. -/
theorem decSim_of_stepOK (hinj : InjOn π N) {i : LinstrRM} {js : List (JInstr 64)}
    (h : stepOK π N i js = true) {zl : Prop} :
    DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K (isCmpB i = true)) [i] js := by
  unfold stepOK at h
  split at h
  · rename_i d opn a
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨hd, ha⟩, h⟩ := h
    exact (unary_sound hinj hd ha h).weaken (fun _ _ _ h => h)
      (fun _ _ _ h => by simpa [isCmpB] using h)
  · rename_i d opn n
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
    obtain ⟨⟨hd, rfl⟩, rfl⟩ := h
    exact (decSim_movImm (Lay := Lay) (frame := frame) (K := K) (zl := zl) d n
      (survives_of_injOn hinj hd)).weaken (fun _ _ _ h => h)
      (fun _ _ _ h => by simpa [isCmpB] using h.dropZf)
  · rename_i d opn a c
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨⟨hd, ha⟩, hc⟩, h⟩ := h
    exact bin_sound hinj hd ha hc h
  · rename_i d opn a k
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨hd, ha⟩, h | h⟩ := h
    · exact imm_sound hinj hd ha h
    · have hnc : isCmpB (.Lopn [.reg d] opn [.reg a, .imm k], .reg none) = false := by
        simp only [shiftOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨⟨rfl, -⟩, -⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> simp [isCmpB, withWidthTag]
      rw [hnc]
      exact (shift_sound ha (survives_of_injOn hinj hd) h).weaken (fun _ _ _ h => h)
        (fun _ _ _ h => by simpa using h)
  · exact absurd h (by simp)

/-- An accepted instruction is an `Lopn`. -/
theorem isLopn_of_stepOK {i : LinstrRM} {js : List (JInstr 64)}
    (h : stepOK π N i js = true) : IsLopn i := by
  unfold stepOK at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact absurd h (by simp)

/-! ## 3. A body -/

/-- A body accepted instruction by instruction, each instruction against its list of
    machine instructions. -/
def bodyOK (π : String → String) (N : List String) :
    List LinstrRM → List (List (JInstr 64)) → Bool
  | [], [] => true
  | i :: is, js :: jss => stepOK π N i js && bodyOK π N is jss
  | _, _ => false

/-- **A body simulates its machine instructions.** By induction over the body, from
    `decSim_of_stepOK` and `DecSim.append`. -/
theorem decSim_of_bodyOK (hinj : InjOn π N) :
    ∀ (is : List LinstrRM) (jss : List (List (JInstr 64))) (zl : Prop),
      bodyOK π N is jss = true →
      DecSim (GCorr π N Lay frame K zl) (GCorr π N Lay frame K False) is jss.flatten := by
  intro is
  induction is with
  | nil =>
    intro jss zl h
    cases jss with
    | nil => exact (DecSim.nil _).weaken (fun _ _ _ h => h) (fun _ _ _ h => h.dropZf)
    | cons _ _ => simp [bodyOK] at h
  | cons i is ih =>
    intro jss zl h
    cases jss with
    | nil => simp [bodyOK] at h
    | cons js jss =>
      simp only [bodyOK, Bool.and_eq_true] at h
      have h1 := decSim_of_stepOK (Lay := Lay) (frame := frame) (K := K) (zl := zl) hinj h.1
      have h2 := ih jss (isCmpB i = true) h.2
      rw [List.flatten_cons]
      exact h1.append h2

theorem isLopn_of_bodyOK :
    ∀ (is : List LinstrRM) (jss : List (List (JInstr 64))),
      bodyOK π N is jss = true → ∀ i ∈ is, IsLopn i := by
  intro is
  induction is with
  | nil => intro _ _ i hi; cases hi
  | cons i is ih =>
    intro jss h x hx
    cases jss with
    | nil => simp [bodyOK] at h
    | cons js jss =>
      simp only [bodyOK, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact isLopn_of_stepOK h.1
      · exact ih jss h.2 x hx

/-! ## 4. The counter register on the machine -/

/-- The decoded loop body writes the register `R` once, by `sub $1, %R`. -/
def decrOnce (R : String) : List (JInstr 64) → Bool
  | [] => false
  | j :: js =>
      if j = .sub R (.imm 1) then js.all (fun j' => !(dsts j').contains R)
      else !(dsts j).contains R && decrOnce R js

theorem runBlock_regs_of_not_dsts (R : String) :
    ∀ (js : List (JInstr 64)) (sa : AState), js.all (fun j => !(dsts j).contains R) = true →
      (aMachine.runBlock sa js).regs R = sa.regs R := by
  intro js
  induction js with
  | nil => intro _ _; rfl
  | cons j js ih =>
    intro sa h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [Machine.runBlock_cons, ih _ h.2]
    have hj : R ∉ dsts j := by simpa using h.1
    exact evalInstrA_regs_of_not_mem_dsts sa j R hj

theorem runBlock_regs_of_decrOnce (R : String) :
    ∀ (js : List (JInstr 64)) (sa : AState), decrOnce R js = true →
      (aMachine.runBlock sa js).regs R = sa.regs R - 1 := by
  intro js
  induction js with
  | nil => intro _ h; simp [decrOnce] at h
  | cons j js ih =>
    intro sa h
    simp only [decrOnce] at h
    split at h
    · rename_i hj
      subst hj
      rw [Machine.runBlock_cons, runBlock_regs_of_not_dsts R js _ h]
      show (if R = R then sa.regs R - BitVec.ofNat 64 1 else sa.regs R) = _
      rw [if_pos rfl]; rfl
    · simp only [Bool.and_eq_true] at h
      rw [Machine.runBlock_cons, ih _ h.2]
      have hj : R ∉ dsts j := by simpa using h.1
      exact congrArg (· - 1) (evalInstrA_regs_of_not_mem_dsts sa j R hj)

/-- The machine compare `cmp $0, %R` leaves the registers unchanged and sets the zero flag
    to the test of `R` against `0`. -/
theorem evalInstrA_cmp0 (sa : AState) (R : String) :
    (evalInstrA sa (.cmp R (.imm 0))).regs = sa.regs
      ∧ (evalInstrA sa (.cmp R (.imm 0))).flags.zf.getD false = (sa.regs R == 0) := by
  refine ⟨rfl, ?_⟩
  show (some (ZF_of_word (sa.regs R - BitVec.ofNat 64 0))).getD false = _
  rw [ZF_of_word_sub]; rfl

/-- A 64-bit word read back from its natural number. -/
theorem ofNat_toNat_bv (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The counter after one decrement: `m - t - 1` for `t < m < 2 ^ 64`. -/
theorem ofNat_sub_one (m t : Nat) (ht : t < m) :
    BitVec.ofNat 64 (m - t) - 1 = BitVec.ofNat 64 (m - (t + 1)) := by
  have e : m - t = (m - (t + 1)) + 1 := by omega
  rw [e, BitVec.ofNat_add]
  simp

/-- The counter is zero exactly on the last trip. -/
theorem ofNat_eq_zero_iff (m t : Nat) (ht : t < m) (hm : m < 2 ^ 64) :
    (BitVec.ofNat 64 (m - (t + 1)) == 0) = true ↔ t + 1 = m := by
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    simp at h2
    omega
  · intro h
    rw [show m - (t + 1) = 0 by omega]
    rfl

/-! ## 5. A node -/

/-- **A checked node on both machines.** The flag-machine node `seeds ++
    guardedFlagLoopLinstrRM top endL ctr body` whose seeds and loop body are accepted by
    `bodyOK` against the machine blocks `jsSeeds` and `jsBody`, with the counter `ctr` live,
    and the decoded node `nodeLayout jsSeeds.flatten l post` whose loop `l` has the counter
    register `π ctr` and the body `jsBody.flatten`, which writes the counter register once by
    `sub $1`. The trip count is the value of the counter register after the seeds. From
    states related by the correspondence on `N`, with the flag machine at program counter
    `0`, the machine halts from index `0` in a state `sa'`, the flag machine halts in `t`, and
    `sa'` is the epilogue `post` run from a state related to `t` by the correspondence. -/
theorem decNode_halts_gen (fn : String) (seeds body : List LinstrRM) (top endL : LLabel)
    (ctr : String) (jsSeeds jsBody : List (List (JInstr 64))) (l : XLoop 64)
    (post : List (JInstr 64)) (hinj : InjOn π N) (hctr : ctr ∈ N)
    (hs : bodyOK π N seeds jsSeeds = true) (hb : bodyOK π N body jsBody = true)
    (hlctr : l.ctr = π ctr) (hlbody : l.body = jsBody.flatten)
    (hdec : decrOnce (π ctr) jsBody.flatten = true)
    (htop : findLabelMem top (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + 2))
    (hend : findLabelMem endL (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + body.length + 5))
    (zl : Prop) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : GCorr π N Lay frame K zl sa b zf) :
    ∃ sa' t k, Halts aMachine (nodeLayout jsSeeds.flatten l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ ∃ sa₀, GCorr π N Lay frame K False sa₀ t.prog.base true
          ∧ sa' = aMachine.runBlock sa₀ post := by
  set R := π ctr with hR
  set m := ((aMachine.runBlock sa jsSeeds.flatten).regs R).toNat with hm
  have hm64 : m < 2 ^ 64 := BitVec.isLt _
  -- the seeds
  have hpre : DecSim (fun sa' b' zf' => GCorr π N Lay frame K zl sa' b' zf' ∧ sa' = sa)
      (fun sa' b' zf' => GCorr π N Lay frame K False sa' b' zf'
        ∧ sa'.regs R = BitVec.ofNat 64 m)
      seeds jsSeeds.flatten :=
    (decSim_of_bodyOK hinj seeds jsSeeds zl hs).andMach (fun sa' h => by
      subst h; rw [hm, ofNat_toNat_bv])
  -- the guard
  have hg : DecSim (fun sa' b' zf' => GCorr π N Lay frame K False sa' b' zf'
        ∧ sa'.regs R = BitVec.ofNat 64 m)
      (fun sa' b' zf' => GCorr π N Lay frame K True sa' b' zf'
        ∧ (sa'.regs R = BitVec.ofNat 64 m
          ∧ sa'.flags.zf.getD false = (sa'.regs R == 0)))
      [cmpRI ctr (.imm 0)] [l.cmpInstr] := by
    have h0 := (decSim_cmpImm (Lay := Lay) (frame := frame) (K := K) (zl := False)
      (L := (· ∈ N)) (π := π) ctr 0 hctr).andMach
      (P := fun sa' => sa'.regs R = BitVec.ofNat 64 m)
      (Q := fun sa' => sa'.regs R = BitVec.ofNat 64 m
        ∧ sa'.flags.zf.getD false = (sa'.regs R == 0)) (fun sa' h => by
        obtain ⟨e1, e2⟩ := evalInstrA_cmp0 sa' R
        simp only [Machine.runBlock_cons, Machine.runBlock_nil]
        exact ⟨by rw [← h, show aMachine.exec = evalInstrA from rfl, e1], by
          rw [show aMachine.exec = evalInstrA from rfl, e2, e1]⟩)
    rw [XLoop.cmpInstr, hlctr]
    exact h0
  -- the trips
  let Inv : Nat → AState → LstateM → Bool → Prop := fun t sa' b' zf' =>
    GCorr π N Lay frame K False sa' b' zf' ∧ sa'.regs R = BitVec.ofNat 64 (m - t)
  let Inv' : Nat → AState → LstateM → Bool → Prop := fun t sa' b' zf' =>
    GCorr π N Lay frame K True sa' b' zf'
      ∧ (sa'.regs R = BitVec.ofNat 64 (m - t) - 1
        ∧ sa'.flags.zf.getD false = (sa'.regs R == 0))
  have hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]) := by
    intro t _
    have hB := (decSim_of_bodyOK (Lay := Lay) (frame := frame) (K := K) hinj body jsBody False
      hb).andMach (P := fun sa' => sa'.regs R = BitVec.ofNat 64 (m - t))
      (Q := fun sa' => sa'.regs R = BitVec.ofNat 64 (m - t) - 1) (fun sa' h => by
        rw [runBlock_regs_of_decrOnce R _ sa' hdec, h])
    have hC := (decSim_cmpImm (Lay := Lay) (frame := frame) (K := K) (zl := False)
      (L := (· ∈ N)) (π := π) ctr 0 hctr).andMach
      (P := fun sa' => sa'.regs R = BitVec.ofNat 64 (m - t) - 1)
      (Q := fun sa' => sa'.regs R = BitVec.ofNat 64 (m - t) - 1
        ∧ sa'.flags.zf.getD false = (sa'.regs R == 0)) (fun sa' h => by
        obtain ⟨e1, e2⟩ := evalInstrA_cmp0 sa' R
        simp only [Machine.runBlock_cons, Machine.runBlock_nil]
        exact ⟨by rw [show aMachine.exec = evalInstrA from rfl, e1, h], by
          rw [show aMachine.exec = evalInstrA from rfl, e2, e1]⟩)
    rw [XLoop.cmpInstr, hlctr, hlbody]
    exact hB.append hC
  obtain ⟨sa', t, k, hh, hrun, hQ⟩ := decNode_halts fn seeds body top endL ctr l m
    (fun sa' b' zf' => GCorr π N Lay frame K zl sa' b' zf' ∧ sa' = sa)
    (fun sa' b' zf' => GCorr π N Lay frame K False sa' b' zf'
      ∧ sa'.regs R = BitVec.ofNat 64 m)
    (fun sa' b' zf' => GCorr π N Lay frame K True sa' b' zf'
      ∧ (sa'.regs R = BitVec.ofNat 64 m ∧ sa'.flags.zf.getD false = (sa'.regs R == 0)))
    Inv Inv'
    (fun sa' b' => ∃ sa₀, GCorr π N Lay frame K False sa₀ b' true
      ∧ sa' = aMachine.runBlock sa₀ post)
    jsSeeds.flatten post
    (isLopn_of_bodyOK seeds jsSeeds hs) (isLopn_of_bodyOK body jsBody hb) htop hend
    hpre hg
    (fun sa' b' zf' ⟨hc, hv, hz⟩ => by
      refine ⟨hc.zfEq trivial, ?_⟩
      rw [← hc.zfEq trivial, hz, hv]
      simp only [beq_iff_eq]
      constructor
      · intro h
        have h2 := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at h2
        simpa using h2
      · intro h; rw [h]; rfl)
    (fun sa' b' zf' pc ⟨hc, hv, _⟩ => ⟨(hc.setLpc pc).dropZf, by rw [hv, Nat.sub_zero]⟩)
    hsim
    (fun t ht sa' b' zf' ⟨hc, hv, hz⟩ => by
      refine ⟨hc.zfEq trivial, ?_⟩
      rw [← hc.zfEq trivial, hz, hv, ofNat_sub_one m t ht]
      exact ofNat_eq_zero_iff m t ht hm64)
    (fun t ht sa' b' zf' pc ⟨hc, hv, _⟩ =>
      ⟨(hc.setLpc pc).dropZf, by rw [hv, ofNat_sub_one m t ht]⟩)
    (fun sa' b' ⟨hc, _⟩ => ⟨sa', hc, rfl⟩)
    sa b zf hpc ⟨hE, rfl⟩
  exact ⟨sa', t, k, hh, hrun, hQ⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
