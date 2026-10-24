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
# Tactics for decoded-instruction simulations

`DecodedLsemStep.DecSim I J ls js` relates a flag-machine segment `ls` to a decoded machine
block `js`. This module states the step lemmas of `DecodedLsemStep` and `DecodedLsemLoop`
with the machine registers as explicit arguments and the equations of the register map
`π` as hypotheses, ending in the live set `liveAfter π L d D`, and packages them as two
tactics.

## The tactics

* `decsim_step` closes one `DecSim` goal of a single flag-machine instruction against its
  machine instructions: register and immediate moves (also elided), count-`0` and
  immediate right shifts, the two-address operations in place and through a copy
  (`ADD`, `SUB`, `AND`, `XOR`, `OR`, `MUL`), the immediate add and subtract, and the
  compares. Each alternative is applied at reducible transparency, and its side
  conditions are closed by `decsim_side`: `rfl`, `assumption`, `decide +kernel`, or
  `simp_all` with the equations of `π` in the context.
* `decsim_chain` splits a list-level `DecSim` goal instruction by instruction
  (`DecSim.cons1`, `DecSim.cons2`, `DecSim.cons0`, and `DecSim.mach_cons` for a
  machine-only register copy), calls `decsim_step` on each pair, and leaves the
  implication from the reached relation to the target relation (`DecSim.of_imp`).

The loads, stores and the high half of the widening multiply carry machine-state side
conditions (frame slots, cell indices, a saved word) and are composed by hand with
`DecSim.frameWith`.

## Main results

* `DecSim.cons0`, `DecSim.cons1`, `DecSim.cons2`, `DecSim.mach_cons`, `DecSim.of_imp`,
  `DecSim.machBlock`: the splitting and closing lemmas the tactics apply.
* `DecSim.frame`, `DecSim.frameWith`: a machine-state predicate carried along a segment.
* `runBlock_regs_of_not_mem`: a block writing none of a list of registers keeps them.
* `DecLsemCorr.mono`: the correspondence on fewer names, cells and flag conditions.
* `decSim_movReg_r` … `decSim_cmpReg_r`: the register-explicit step lemmas.
* `decSim_shrImm_mov`: `SHR:k:64` against a copy and `shr`.
* `decSim_mulhi_bracket`: `MULXHI:64` against the fused `mulx` site whose implicit
  source register is saved to and restored from a third register.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
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

/-! ## 1. Splitting a segment -/

/-- A flag-machine segment `i :: ls` against a machine block `pre ++ js`, the first
    instruction against `pre`. -/
theorem DecSim.cons_pre {I J M : AState → LstateM → Bool → Prop} {i : LinstrRM}
    {ls : List LinstrRM} (pre js : List (JInstr 64))
    (h₁ : DecSim I J [i] pre) (h₂ : DecSim J M ls js) :
    DecSim I M (i :: ls) (pre ++ js) :=
  DecSim.append h₁ h₂

/-- The first flag-machine instruction with no machine instruction. -/
theorem DecSim.cons0 {I J M : AState → LstateM → Bool → Prop} {i : LinstrRM}
    {ls : List LinstrRM} {js : List (JInstr 64)}
    (h₁ : DecSim I J [i] []) (h₂ : DecSim J M ls js) : DecSim I M (i :: ls) js :=
  DecSim.cons_pre [] js h₁ h₂

/-- The first flag-machine instruction against one machine instruction. -/
theorem DecSim.cons1 {I J M : AState → LstateM → Bool → Prop} {i : LinstrRM}
    {ls : List LinstrRM} {j₁ : JInstr 64} {js : List (JInstr 64)}
    (h₁ : DecSim I J [i] [j₁]) (h₂ : DecSim J M ls js) : DecSim I M (i :: ls) (j₁ :: js) :=
  DecSim.cons_pre [j₁] js h₁ h₂

/-- The first flag-machine instruction against two machine instructions. -/
theorem DecSim.cons2 {I J M : AState → LstateM → Bool → Prop} {i : LinstrRM}
    {ls : List LinstrRM} {j₁ j₂ : JInstr 64} {js : List (JInstr 64)}
    (h₁ : DecSim I J [i] [j₁, j₂]) (h₂ : DecSim J M ls js) :
    DecSim I M (i :: ls) (j₁ :: j₂ :: js) :=
  DecSim.cons_pre [j₁, j₂] js h₁ h₂

/-- A machine instruction with no flag-machine instruction in front of a segment. -/
theorem DecSim.mach_cons {I J M : AState → LstateM → Bool → Prop} {j : JInstr 64}
    {ls : List LinstrRM} {js : List (JInstr 64)}
    (h₁ : DecSim I J [] [j]) (h₂ : DecSim J M ls js) : DecSim I M ls (j :: js) :=
  DecSim.append h₁ h₂

/-- The empty segment from `I` to `J` when `I` implies `J`. -/
theorem DecSim.of_imp {I J : AState → LstateM → Bool → Prop}
    (h : ∀ sa b zf, I sa b zf → J sa b zf) : DecSim I J [] [] :=
  DecSim.weaken (DecSim.nil I) (fun _ _ _ hi => hi) h

/-- A machine block with no flag-machine instruction. -/
theorem DecSim.machBlock {I J : AState → LstateM → Bool → Prop} {js : List (JInstr 64)}
    (h : ∀ sa b zf, I sa b zf → J (aMachine.runBlock sa js) b zf) : DecSim I J [] js :=
  fun sa b zf hi => ⟨b, zf, rfl, h sa b zf hi⟩

/-- A machine-state predicate `P` carried to `Q` by the machine block alone, on top of a
    segment simulation. -/
theorem DecSim.frame {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (P Q : AState → Prop) (h : DecSim I J ls js)
    (hPQ : ∀ sa, P sa → Q (aMachine.runBlock sa js)) :
    DecSim (fun sa b zf => I sa b zf ∧ P sa) (fun sa b zf => J sa b zf ∧ Q sa) ls js :=
  fun sa b zf hip => by
    obtain ⟨b₁, z₁, hr, hj⟩ := h sa b zf hip.1
    exact ⟨b₁, z₁, hr, hj, hPQ sa hip.2⟩

/-- A segment simulation whose precondition carries a machine-state fact `Q`, run from a
    machine-state predicate `P` that implies `Q` and that the block carries to `P'`. -/
theorem DecSim.frameWith {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (Q P P' : AState → Prop)
    (h : DecSim (fun sa b zf => I sa b zf ∧ Q sa) J ls js) (hQ : ∀ sa, P sa → Q sa)
    (hP : ∀ sa, P sa → P' (aMachine.runBlock sa js)) :
    DecSim (fun sa b zf => I sa b zf ∧ P sa) (fun sa b zf => J sa b zf ∧ P' sa) ls js :=
  fun sa b zf hip => by
    obtain ⟨b₁, z₁, hr, hj⟩ := h sa b zf ⟨hip.1, hQ sa hip.2⟩
    exact ⟨b₁, z₁, hr, hj, hP sa hip.2⟩

/-- One step of the machine is `evalInstrA`. -/
theorem aMachine_exec (s : AState) (i : JInstr 64) : aMachine.exec s i = evalInstrA s i := rfl

/-- A machine block writes no register of `Rs`, so the block keeps their values. -/
theorem runBlock_regs_of_not_mem (Rs : List String) :
    ∀ (js : List (JInstr 64)) (sa : AState), (∀ j ∈ js, ∀ R ∈ Rs, R ∉ dsts j) →
      ∀ R ∈ Rs, (aMachine.runBlock sa js).regs R = sa.regs R
  | [], _, _, _, _ => rfl
  | j :: js, sa, h, R, hR => by
    rw [Machine.runBlock_cons,
      runBlock_regs_of_not_mem Rs js _ (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')) R hR]
    exact evalInstrA_regs_of_not_mem_dsts sa j R (h j List.mem_cons_self R hR)

/-- The correspondence on fewer live names, fewer cells and a weaker flag condition. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep.DecLsemCorr.mono
    {π : String → String} {L L' : String → Prop} {Lay : Layout}
    {frame : String → Option (BitVec 64)} {K K' : String → Nat → Prop} {zl zl' : Prop}
    {sa : AState} {b : LstateM} {zf : Bool} (h : DecLsemCorr π L Lay frame K zl sa b zf)
    (hL : ∀ r, L' r → L r) (hz : zl' → zl) (hK : ∀ A j, K' A j → K A j) :
    DecLsemCorr π L' Lay frame K' zl' sa b zf where
  regs r hr := h.regs r (hL r hr)
  zfEq hz' := h.zfEq (hz hz')
  cells A j hk := h.cells A j (hK A j hk)
  slots := h.slots

/-! ## 2. Stack words -/

/-- Disjoint words are distinct. -/
theorem ne_of_disjoint8 {a b : BitVec 64} (h : Disjoint8 a b) : b ≠ a := by
  rintro rfl
  have := h.1
  simp at this

/-- `Disjoint8` is invariant under a common translation. -/
theorem disjoint8_add_left (x a c : BitVec 64) (h : Disjoint8 a c) :
    Disjoint8 (x + a) (x + c) := by
  unfold Disjoint8 at *
  rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
  exact h

/-- Two stack words at offsets `o₁`, `o₂` from one base are disjoint when the offsets are. -/
theorem disjoint8_off (x : BitVec 64) (o₁ o₂ : Int)
    (h : Disjoint8 (BitVec.ofInt 64 o₁) (BitVec.ofInt 64 o₂)) :
    Disjoint8 (x + BitVec.ofInt 64 o₁) (x + BitVec.ofInt 64 o₂) :=
  disjoint8_add_left x _ _ h

theorem ofNat_toNat_lt (t : Nat) (ht : t < 2 ^ 64) : (BitVec.ofNat 64 t).toNat = t := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt ht

theorem ofNat_beq_zero_iff (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = true ↔ n = 0 := by
  rw [beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [ofNat_toNat_lt n hn] at this
    simpa using this
  · rintro rfl; rfl

/-! ## 3. Register-explicit forms of the step lemmas

Each form names the machine registers of the instruction, takes the equations of `π` at
the names, and ends in the live set `liveAfter π L d D`, so that it unifies with a block
of literal registers and leaves no live set to choose. -/

/-- The live names after a write of `d` to the machine register `D`: `d`, and the names
    live before whose register is not `D`. -/
abbrev liveAfter (π : String → String) (L : String → Prop) (d D : String) : String → Prop :=
  fun r => r = d ∨ (L r ∧ π r ≠ D)

/-- The live names after a machine write to `D`: those live before whose register is not
    `D`. -/
abbrev liveOff (π : String → String) (L : String → Prop) (D : String) : String → Prop :=
  fun r => L r ∧ π r ≠ D

variable {π : String → String} {L : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}

theorem decSim_movReg_r (d s D S : String) (hD : π d = D) (hS : π s = S) (hs : L s) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π (liveAfter π L d D) Lay frame K zl)
      [movRI d s] [.mov D (.reg S)] := by
  subst hD hS; exact decSim_movReg d s hs (fun _ hr => hr)

theorem decSim_movReg_elided_r (d s : String) (hs : L s) (hds : π d = π s) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K zl) [movRI d s] [] :=
  decSim_movReg_elided d s hs hds (fun _ hr => hr)

theorem decSim_movImm_r (d D : String) (n : Nat) (hD : π d = D) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π (liveAfter π L d D) Lay frame K zl)
      [movII d n] [.mov D (.imm n)] := by
  subst hD; exact decSim_movImm d n (fun _ hr => hr)

theorem decSim_shl0_r (d a D A : String) (hD : π d = D) (hA : π a = A) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π (liveAfter π L d D) Lay frame K zl)
      [immShiftI "SHL" d a 0] [.mov D (.reg A)] := by
  subst hD hA; exact decSim_shl0 d a ha (fun _ hr => hr)

theorem decSim_shl0_elided_r (d a : String) (ha : L a) (hda : π d = π a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d (π d)) Lay frame K zl) [immShiftI "SHL" d a 0] [] :=
  decSim_shl0_elided d a ha hda (fun _ hr => hr)

theorem decSim_shrImm_r (d a D : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (hD : π d = D)
    (hA : π a = D) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [immShiftI "SHR" d a k] [.shr D (.imm k)] := by
  subst hD; exact decSim_shrImm d a k hk0 hk ha hA.symm (fun _ hr => hr)

/-- `SHR:k:64 d, a` against the copy `mov %a, %d` and `shr $k, %d`, `0 < k < 64`. -/
theorem decSim_shrImm_mov (d a D A : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64)
    (hD : π d = D) (hA : π a = A) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [immShiftI "SHR" d a k] [.mov D (.reg A), .shr D (.imm k)] := by
  subst hD hA
  intro sa b zf h
  refine ⟨_, zf, ?_, h.write d (sa.regs (π a) >>> k) _ (fun r => ?_) rfl (fun _ hr => hr)
    (fun hz => hz.elim)⟩
  · rw [runStraightF_singleton]; exact fstepF_shrImmI d a k hk b zf _ (h.regs a ha)
  · show (if r = π d then (x86_SHR ((evalInstrA sa (.mov (π d) (.reg (π a)))).regs (π d))
        (BitVec.ofNat 64 k)).word else (evalInstrA sa (.mov (π d) (.reg (π a)))).regs r) = _
    have e : ∀ x, (evalInstrA sa (.mov (π d) (.reg (π a)))).regs x
        = if x = π d then sa.regs (π a) else sa.regs x := fun _ => rfl
    rw [e, e, ite_eq_left rfl, x86_SHR_word_imm _ k hk0 hk]
    split <;> rfl

theorem decSim_addImm_r (d a D : String) (k : Nat) (hD : π d = D) (hA : π a = D) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [addImmI d a k] [.add D (.imm k)] := by
  subst hD; exact decSim_addImm d a k ha hA.symm (fun _ hr => hr)

theorem decSim_subImm_r (d a D : String) (k : Nat) (hD : π d = D) (hA : π a = D) (ha : L a) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [subImmI d a k] [.sub D (.imm k)] := by
  subst hD; exact decSim_subImm d a k ha hA.symm (fun _ hr => hr)

theorem decSim_cmpImm_r (c C : String) (k : Nat) (hC : π c = C) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L Lay frame K True)
      [cmpRI c (.imm k)] [.cmp C (.imm k)] := by
  subst hC; exact decSim_cmpImm c k hc

theorem decSim_cmpReg_r (c r C R : String) (hC : π c = C) (hR : π r = R) (hc : L c)
    (hr : L r) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L Lay frame K True)
      [cmpRI c (.reg r)] [.cmp C (.reg R)] := by
  subst hC hR; exact decSim_cmpReg c r hc hr

/-- A two-address operation in place: `opn d, a, c` against `mk %c, %d` with `d` and `a`
    in the register `D`. The instances fix `opn`, its base mnemonic, `f` and `mk`. -/
theorem decSim_binReg_r (opn base : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI opn d a c] [mk D (.reg C)] := by
  subst hD hC
  exact decSim_binReg opn base hstrip hcmp hmul hcarry f hf mk hmk hmkm d a c ha hc hA.symm
    (fun _ hr => hr)

/-- A two-address operation through a copy: `opn d, a, c` against `mov %a, %d` and
    `mk %c, %d`, the registers `C` of `c` and `D` of `d` distinct. -/
theorem decSim_binReg_mov_r (opn base : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C) (hCD : C ≠ D)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI opn d a c] [.mov D (.reg A), mk D (.reg C)] := by
  subst hD hA hC
  exact decSim_binReg_mov opn base hstrip hcmp hmul hcarry f hf mk hmk hmkm d a c ha hc hCD
    (fun _ hr => hr)

theorem decSim_add_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "ADD:64" d a c] [.add D (.reg C)] :=
  decSim_binReg_r _ "ADD"
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond.stripWidthTag_ADD64
    (by decide +kernel) (by decide) (by decide)
    (· + ·) (fun _ _ => rfl) JInstr.add (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_sub_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "SUB:64" d a c] [.sub D (.reg C)] :=
  decSim_binReg_r _ "SUB"
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond.stripWidthTag_SUB64
    (by decide +kernel) (by decide) (by decide)
    (· - ·) (fun _ _ => rfl) JInstr.sub (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_and_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "AND:64" d a c] [.and_ D (.reg C)] :=
  decSim_binReg_r _ "AND" stripWidthTag_AND64 (by decide +kernel) (by decide) (by decide)
    (· &&& ·)
    (fun _ _ => rfl) JInstr.and_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_xor_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "XOR:64" d a c] [.xor_ D (.reg C)] :=
  decSim_binReg_r _ "XOR" stripWidthTag_XOR64 (by decide +kernel) (by decide) (by decide)
    (· ^^^ ·)
    (fun _ _ => rfl) JInstr.xor_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_or_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "OR:64" d a c] [.or_ D (.reg C)] :=
  decSim_binReg_r _ "OR" stripWidthTag_OR64 (by decide +kernel) (by decide) (by decide)
    (· ||| ·)
    (fun _ _ => rfl) JInstr.or_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_imul_r (d a c D C : String) (hD : π d = D) (hA : π a = D) (hC : π c = C)
    (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "MUL:64" d a c] [.imul D (.reg C)] :=
  decSim_binReg_r _ "MUL" stripWidthTag_MUL64 (by decide +kernel) (by decide) (by decide)
    (· * ·)
    (fun _ _ => rfl) JInstr.imul (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D C hD hA hC ha hc

theorem decSim_add_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "ADD:64" d a c] [.mov D (.reg A), .add D (.reg C)] :=
  decSim_binReg_mov_r _ "ADD"
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond.stripWidthTag_ADD64
    (by decide +kernel) (by decide) (by decide)
    (· + ·) (fun _ _ => rfl) JInstr.add (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) d a c D A C hD hA hC hCD ha hc

theorem decSim_sub_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "SUB:64" d a c] [.mov D (.reg A), .sub D (.reg C)] :=
  decSim_binReg_mov_r _ "SUB"
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond.stripWidthTag_SUB64
    (by decide +kernel) (by decide) (by decide)
    (· - ·) (fun _ _ => rfl) JInstr.sub (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) d a c D A C hD hA hC hCD ha hc

theorem decSim_and_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "AND:64" d a c] [.mov D (.reg A), .and_ D (.reg C)] :=
  decSim_binReg_mov_r _ "AND" stripWidthTag_AND64 (by decide +kernel) (by decide) (by decide)
    (· &&& ·)
    (fun _ _ => rfl) JInstr.and_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D A C hD hA hC
    hCD ha hc

theorem decSim_xor_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "XOR:64" d a c] [.mov D (.reg A), .xor_ D (.reg C)] :=
  decSim_binReg_mov_r _ "XOR" stripWidthTag_XOR64 (by decide +kernel) (by decide) (by decide)
    (· ^^^ ·)
    (fun _ _ => rfl) JInstr.xor_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D A C hD hA hC
    hCD ha hc

theorem decSim_or_mov (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "OR:64" d a c] [.mov D (.reg A), .or_ D (.reg C)] :=
  decSim_binReg_mov_r _ "OR" stripWidthTag_OR64 (by decide +kernel) (by decide) (by decide)
    (· ||| ·)
    (fun _ _ => rfl) JInstr.or_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) d a c D A C hD hA hC
    hCD ha hc

theorem decSim_imul_mov_r (d a c D A C : String) (hD : π d = D) (hA : π a = A) (hC : π c = C)
    (hCD : C ≠ D) (ha : L a) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π L d D) Lay frame K False)
      [binRegI "MUL:64" d a c] [.mov D (.reg A), .imul D (.reg C)] := by
  subst hD hA hC; exact decSim_imul_mov d a c ha hc hCD (fun _ hr => hr)

theorem decSim_machMov_r (D S : String) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π (liveOff π L D) Lay frame K zl)
      [] [.mov D (.reg S)] :=
  decSim_machMov D S (fun _ hr => hr)

/-- **High half, bracketed.** `MULXHI:64 hi, a, c` against the fused site of
    `fuseMulHiLprog` with the implicit-source register `S` kept through `T`: the copy
    `mov %S, %T`, the pin `mov %a, %S`, the save of `D` to `off(%SP)`,
    `mulx %c, %D, %hi` with implicit source `S`, the reload of `D`, and the restore
    `mov %T, %S`. Afterwards `S` and `D` hold their values from before, `T` holds the old
    value of `S`, and the names in `T` are dropped from the live set. -/
theorem decSim_mulhi_bracket (hi a c S D T SP : String) (off : Int) (ha : L a) (hc : L c)
    (hTS : T ≠ S) (hTSP : T ≠ SP) (hTD : T ≠ D) (hTH : T ≠ π hi) (hSSP : S ≠ SP)
    (hSD : S ≠ D) (hSH : S ≠ π hi) (hDSP : D ≠ SP) (hDH : D ≠ π hi) (hSPH : SP ≠ π hi)
    (haT : π a ≠ T) (hcS : π c ≠ S) (hcT : π c ≠ T) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
        ∧ (∀ A j, K A j → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) (Lay.addr A j))
        ∧ (∀ q x, frame q = some x → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) x))
      (DecLsemCorr π (liveAfter π (liveOff π L T) hi (π hi)) Lay frame K zl) [mulhiI hi a c]
      [.mov T (.reg S), .mov S (.reg (π a)), .storeMem SP off (.reg D),
        .mulx (π hi) D (.reg S) (.reg (π c)), .loadMem D SP off, .mov S (.reg T)] := by
  intro sa b zf ⟨h, hK, hF⟩
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have emm : ∀ (s : AState) (X Y : String), (evalInstrA s (.mov X (.reg Y))).mem = s.mem :=
    fun _ _ _ => rfl
  have exm : ∀ (s : AState) (H X Y Z : String),
      (evalInstrA s (.mulx H X (.reg Y) (.reg Z))).mem = s.mem := fun _ _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have hc1 := DecLsemCorr.memWrite h (sa.regs SP + BitVec.ofInt 64 off) (sa.regs D)
    { sa with mem := write64 sa.mem (sa.regs SP + BitVec.ofInt 64 off) (sa.regs D) }
    rfl rfl rfl hK hF
  have hc2 := hc1.machWrite (L' := liveOff π L T) (zl' := zl) T (sa.regs S)
    { sa with mem := write64 sa.mem (sa.regs SP + BitVec.ofInt 64 off) (sa.regs D),
              regs := fun r => if r = T then sa.regs S else sa.regs r }
    (fun _ => rfl) rfl (fun _ hr => hr) (fun hz => h.zfEq hz)
  refine ⟨_, zf, by
    rw [runStraightF_singleton]; exact fstepF_mulhiI hi a c b zf _ _ (h.regs a ha) (h.regs c hc),
    hc2.write hi _ _ (fun r => ?_) ?_ (fun _ hr => hr) (fun hz => h.zfEq hz)⟩
  · show (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
      (.mov T (.reg S))) (.mov S (.reg (π a)))) (.storeMem SP off (.reg D)))
      (.mulx (π hi) D (.reg S) (.reg (π c)))) (.loadMem D SP off)) (.mov S (.reg T))).regs r = _
    simp only [em, evalInstrA_loadMem_regs', evalInstrA_mulx_regs, es, esm, emm, exm,
      ite_eq_right hTD, ite_eq_right hDSP.symm, ite_eq_right hSSP.symm, ite_eq_right hTSP.symm, ite_eq_right hTS, ite_eq_right hcS,
      ite_eq_right hcT, ite_eq_right haT, ite_eq_right hTH, ite_eq_right hSD.symm, ite_eq_right hTD.symm, ite_eq_right hSPH, ite_true,
      read64_write64_same]
    by_cases h1 : r = S
    · subst h1; rw [ite_eq_left rfl, ite_eq_right hSH, ite_eq_right hTS.symm]
    · rw [ite_eq_right h1]
      by_cases h2 : r = D
      · subst h2; rw [ite_eq_left rfl, ite_eq_right hDH, ite_eq_right hTD.symm]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
        by_cases h3 : r = π hi
        · rw [ite_eq_left h3, ite_eq_left h3]; rfl
        · rw [ite_eq_right h3, ite_eq_right h3]
  · show (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
      (.mov T (.reg S))) (.mov S (.reg (π a)))) (.storeMem SP off (.reg D)))
      (.mulx (π hi) D (.reg S) (.reg (π c)))) (.loadMem D SP off)) (.mov S (.reg T))).mem = _
    simp only [emm, elm, exm, esm, em, ite_eq_right hSSP.symm, ite_eq_right hTSP.symm, ite_eq_right hSD.symm,
      ite_eq_right hTD.symm]

/-- **High half, bracketed, with the low half dropped.** `MULXHI:64 hi, a, c` against the
    copy `mov %S, %T`, the pin `mov %a, %S`, `mulx %c, %D, %hi` with implicit source `S` and
    the restore `mov %T, %S`. Afterwards `S` holds its value from before, `T` the old value of
    `S` and `D` the low half; the names in `T` and in `D` are dropped from the live set. -/
theorem decSim_mulhi_bracketD (hi a c S D T : String) (ha : L a) (hc : L c)
    (hTS : T ≠ S) (hTD : T ≠ D) (hTH : T ≠ π hi) (hSD : S ≠ D) (hSH : S ≠ π hi)
    (hDH : D ≠ π hi) (haT : π a ≠ T) (hcS : π c ≠ S) (hcT : π c ≠ T) :
    DecSim (DecLsemCorr π L Lay frame K zl)
      (DecLsemCorr π (liveAfter π (liveOff π (liveOff π L T) D) hi (π hi)) Lay frame K zl)
      [mulhiI hi a c]
      [.mov T (.reg S), .mov S (.reg (π a)), .mulx (π hi) D (.reg S) (.reg (π c)),
        .mov S (.reg T)] := by
  intro sa b zf h
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emm : ∀ (s : AState) (X Y : String), (evalInstrA s (.mov X (.reg Y))).mem = s.mem :=
    fun _ _ _ => rfl
  have exm : ∀ (s : AState) (H X Y Z : String),
      (evalInstrA s (.mulx H X (.reg Y) (.reg Z))).mem = s.mem := fun _ _ _ _ _ => rfl
  have hc1 := h.machWrite (L' := liveOff π L T) (zl' := zl) T (sa.regs S)
    { sa with regs := fun r => if r = T then sa.regs S else sa.regs r }
    (fun _ => rfl) rfl (fun _ hr => hr) (fun hz => h.zfEq hz)
  have hc2 := hc1.machWrite (L' := liveOff π (liveOff π L T) D) (zl' := zl) D
    (x86_MULX_lo_hi (sa.regs (π a)) (sa.regs (π c))).1
    { sa with regs := fun r => if r = D then (x86_MULX_lo_hi (sa.regs (π a)) (sa.regs (π c))).1
        else if r = T then sa.regs S else sa.regs r }
    (fun _ => rfl) rfl (fun _ hr => hr) (fun hz => h.zfEq hz)
  refine ⟨_, zf, by
    rw [runStraightF_singleton]; exact fstepF_mulhiI hi a c b zf _ _ (h.regs a ha) (h.regs c hc),
    hc2.write hi _ _ (fun r => ?_) ?_ (fun _ hr => hr) (fun hz => h.zfEq hz)⟩
  · show (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
      (.mov T (.reg S))) (.mov S (.reg (π a))))
      (.mulx (π hi) D (.reg S) (.reg (π c)))) (.mov S (.reg T))).regs r = _
    simp only [em, evalInstrA_mulx_regs, ite_eq_right hTS, ite_eq_right hcS, ite_eq_right hcT, ite_eq_right haT,
      ite_eq_right hTH, ite_eq_right hTD, ite_true]
    by_cases h1 : r = S
    · subst h1; rw [ite_eq_left rfl, ite_eq_right hSH, ite_eq_right hSD, ite_eq_right hTS.symm]
    · rw [ite_eq_right h1]
      by_cases h3 : r = π hi
      · rw [ite_eq_left h3, ite_eq_left h3]; rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        by_cases h2 : r = D
        · rw [ite_eq_left h2, ite_eq_left h2]
        · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
  · show (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
      (.mov T (.reg S))) (.mov S (.reg (π a))))
      (.mulx (π hi) D (.reg S) (.reg (π c)))) (.mov S (.reg T))).mem = _
    simp only [emm, exm]

/-! ## 4. The tactics -/

/-- Side conditions of the register-explicit step lemmas: equations of the register map,
    register-name inequalities and live-set membership. With `π` a concrete function they
    close by evaluation; with `π` given by equations in the context, by rewriting. -/
syntax "decsim_side" : tactic
macro_rules
  | `(tactic| decsim_side) =>
    `(tactic| first
      | rfl
      | assumption
      | decide +kernel
      | (simp_all (config := { decide := true }) [liveAfter, liveOff]; done))

/-- Closes every side condition a step lemma leaves by `decsim_side`. -/
syntax "decsim_close" : tactic
macro_rules
  | `(tactic| decsim_close) => `(tactic| all_goals decsim_side)

/-- Closes one `DecSim` goal of a single flag-machine instruction against its machine
    instructions, by the first register-explicit step lemma whose side conditions
    `decsim_side` closes. -/
syntax "decsim_step" : tactic
macro_rules
  | `(tactic| decsim_step) =>
    `(tactic| focus first
      | (with_reducible apply decSim_movReg_r; decsim_close)
      | (with_reducible apply decSim_movReg_elided_r; decsim_close)
      | (with_reducible apply decSim_movImm_r; decsim_close)
      | (with_reducible apply decSim_shl0_r; decsim_close)
      | (with_reducible apply decSim_shl0_elided_r; decsim_close)
      | (with_reducible apply decSim_shrImm_r; decsim_close)
      | (with_reducible apply decSim_shrImm_mov; decsim_close)
      | (with_reducible apply decSim_add_r; decsim_close)
      | (with_reducible apply decSim_sub_r; decsim_close)
      | (with_reducible apply decSim_and_r; decsim_close)
      | (with_reducible apply decSim_xor_r; decsim_close)
      | (with_reducible apply decSim_or_r; decsim_close)
      | (with_reducible apply decSim_imul_r; decsim_close)
      | (with_reducible apply decSim_add_mov; decsim_close)
      | (with_reducible apply decSim_sub_mov; decsim_close)
      | (with_reducible apply decSim_and_mov; decsim_close)
      | (with_reducible apply decSim_xor_mov; decsim_close)
      | (with_reducible apply decSim_or_mov; decsim_close)
      | (with_reducible apply decSim_imul_mov_r; decsim_close)
      | (with_reducible apply decSim_addImm_r; decsim_close)
      | (with_reducible apply decSim_subImm_r; decsim_close)
      | (with_reducible apply decSim_cmpImm_r; decsim_close)
      | (with_reducible apply decSim_cmpReg_r; decsim_close))

/-- One split of `decsim_chain`: the first flag-machine instruction against the first one,
    two or zero machine instructions, in that order, or one machine-only register copy. -/
syntax "decsim_cons" : tactic
macro_rules
  | `(tactic| decsim_cons) =>
    `(tactic| first
      | (with_reducible apply DecSim.cons1; on_goal 1 => decsim_step)
      | (with_reducible apply DecSim.cons2; on_goal 1 => decsim_step)
      | (with_reducible apply DecSim.cons0; on_goal 1 => decsim_step)
      | (with_reducible apply DecSim.mach_cons
         on_goal 1 => with_reducible apply decSim_machMov_r))

/-- Splits a `DecSim` goal over a flag-machine segment and a machine block instruction by
    instruction with `decsim_cons`, down to the empty segment, where it leaves the
    implication between the reached relation and the target relation. -/
syntax "decsim_chain" : tactic
macro_rules
  | `(tactic| decsim_chain) =>
    `(tactic| first
      | apply DecSim.of_imp
      | (decsim_cons; decsim_chain))

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
