/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep

@[expose] public section

set_option autoImplicit false

/-!
# Decoded loops against the flag machine

`DecodedLsemStep` relates the address machine `RInstrAddrMem.aMachine` running decoded
instructions to the flag machine `lsemFuelMemF`, one straight segment at a time
(`DecSim`). This module adds the counted loop, its zero-trip guard, and a whole node.

## The loop

The flag machine's guarded loop `guardedFlagLoopLinstrRM top endL ctr body` is the guard
`CMP ctr, #0 ; Lcond Z endL`, the label `top`, the body, the back-edge
`CMP ctr, #0 ; Lcond NZ top` and the label `endL`. Its decoded counterpart
`guardedLayout pre l rest` is `pre`, the guard `cmp ctr, 0 ; je exit`, the pass
`l.body ++ [l.cmpInstr]`, the back-edge `jne head` and `rest`. The hypotheses are
trip-indexed: for each trip `t < m` the body with its back-edge compare simulates the pass
from `Inv t` to `Inv' t`, and `Inv' t` fixes the machine zero flag to the flag-machine
flag, which holds exactly after the last trip.

## Main results

* `decLoop_trips`: the region do-while `runFRegionF` and the machine loop
  `Machine.runXLoop` run the same number of passes and end related by `Inv m`.
* `decLoop_guarded_run`, `decLoop_guarded`: the guarded loop, including the zero-trip skip,
  as the spec fold `runFB` and on `lsemFuelMemF`, against `Reaches` over `guardedLayout`.
* `decNode_halts`: a node `seeds ++ guardedFlagLoopLinstrRM …` against
  `nodeLayout pre l post`: the machine halts, the flag machine halts, and the end states
  satisfy the exit relation.
* `lsemFuelMemF_det`: two terminating flag-machine runs from one state agree.
* `decSim_mulhi`, `decSim_mulhi_saved`, `decSim_mulhi_pinned`: the high half `MULXHI:64`
  alone against the `mulx` of `FheMontMulEmit.fuseMulHiLprog`, which keeps the low
  `MUL:64` in place, so the two halves are simulated independently of what lies between
  them.
* `decSim_binReg_mov`, `decSim_imul_mov`: a three-address operation against the copy and
  the two-address instruction of the legalised body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)
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

/-! ## 1. The back-edge compare, inverted -/

/-- A successful flag compare `CMP:64 c, #k` read the counter `c` at width `64`, moved only
    the program counter, and set the flag to the equality of the counter with `k`. -/
theorem fstepF_cmpRI_imm_inv (c : String) (k : Nat) (b : LstateM) (zf : Bool) (b' : LstateM)
    (z' : Bool) (h : fstepF (cmpRI c (.imm k)) b zf = some (b', z')) :
    ∃ v, b.reg.getW c 64 = some v ∧ b' = b.nextPc ∧ z' = (v == BitVec.ofNat 64 k) := by
  cases hv : b.reg.getW c 64 with
  | none =>
    have hc' : evalOperandN b.reg 64 (.reg c) = none := hv
    simp [fstepF, cmpRI, cmpArgs?, hc'] at h
  | some v =>
    rw [fstepF_cmpRI c (.imm k) b zf v (BitVec.ofNat 64 k) hv rfl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨v, rfl, rfl, rfl⟩

/-- A successful fold of a body followed by `CMP:64 c, #0` is the fold of the body, then a
    counter read, with the flag the equality of the counter with `0`. -/
theorem runStraightF_snoc_cmp_inv (body : List LinstrRM) (c : String) (s : LstateM)
    (zf : Bool) (b' : LstateM) (z' : Bool)
    (h : runStraightF (body ++ [cmpRI c (.imm 0)]) s zf = some (b', z')) :
    ∃ b₁ z₁ v, runStraightF body s zf = some (b₁, z₁) ∧ b₁.reg.getW c 64 = some v
      ∧ b' = b₁.nextPc ∧ z' = (v == 0#64) := by
  rw [runStraightF_append] at h
  cases hb : runStraightF body s zf with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bz =>
    rw [hb, Option.bind_some, runStraightF_singleton] at h
    obtain ⟨v, hv, rfl, rfl⟩ := fstepF_cmpRI_imm_inv c 0 bz.1 bz.2 b' z' h
    exact ⟨bz.1, bz.2, v, rfl, hv, rfl, rfl⟩

/-! ## 2. The loop -/

/-- **The counted loop, trip by trip.** Let the body `body` followed by `CMP:64 ctr, #0`
    simulate the machine pass `l.body ++ [l.cmpInstr]` from `Inv t` to `Inv' t` for each
    trip `t < m`, with `Inv' t` fixing the machine zero flag to the flag-machine flag, which
    holds exactly after the last trip, and `Inv' t` giving `Inv (t + 1)` at any program
    counter. From a state in `Inv t` with `t + k + 1 = m`, the flag machine's region
    do-while and the machine's counted loop both run `k + 1` passes and end in states
    related by `Inv m` at any program counter. -/
theorem decLoop_trips (ctr : String) (body : List LinstrRM) (l : XLoop 64) (q m : Nat)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf) :
    ∀ k t, t + k + 1 = m → ∀ sa b zf, Inv t sa b zf →
      ∃ sa' b', runFRegionF (k + 1) ctr [.straight body] q b zf = some (b', true)
        ∧ aMachine.runXLoop (k + 1) sa l = some sa'
        ∧ ∀ pc, Inv m sa' (b'.setLpc pc) true := by
  intro k
  induction k with
  | zero =>
    intro t htm sa b zf hI
    obtain ⟨b₂, z₂, hr, hJ⟩ := hsim t (by omega) sa b zf hI
    obtain ⟨b₁, z₁, v, hr₁, hv, rfl, rfl⟩ := runStraightF_snoc_cmp_inv body ctr b zf b₂ z₂ hr
    obtain ⟨hzf, hlast⟩ := hflag t (by omega) _ _ _ hJ
    have hz : (v == 0#64) = true := hlast.2 (by omega)
    refine ⟨aMachine.pass l sa, b₁.setLpc (q + (flatFL [.straight body]).length + 2), ?_, ?_,
      fun pc => ?_⟩
    · rw [runFRegionF_succ, runFBsL_straight, hr₁, Option.bind_some]
      simp only [hv, hz, if_true]
    · have hf : (aMachine.view (aMachine.pass l sa)).flagB (·.zf) = true := by
        rw [← hz]; exact hzf
      simp only [Machine.runXLoop, hf, if_true]
    · have := hnext t (by omega) _ _ _ pc hJ
      rw [hz, show t + 1 = m by omega] at this
      exact this
  | succ k ih =>
    intro t htm sa b zf hI
    obtain ⟨b₂, z₂, hr, hJ⟩ := hsim t (by omega) sa b zf hI
    obtain ⟨b₁, z₁, v, hr₁, hv, rfl, rfl⟩ := runStraightF_snoc_cmp_inv body ctr b zf b₂ z₂ hr
    obtain ⟨hzf, hlast⟩ := hflag t (by omega) _ _ _ hJ
    have hz : (v == 0#64) = false := by
      cases h' : (v == 0#64)
      · rfl
      · exact absurd (hlast.1 h') (by omega)
    have hI' := hnext t (by omega) _ _ _ q hJ
    rw [hz] at hI'
    obtain ⟨sa', b', hreg, hmach, hInv⟩ := ih (t + 1) (by omega) _ _ _ hI'
    refine ⟨sa', b', ?_, ?_, hInv⟩
    · rw [runFRegionF_succ, runFBsL_straight, hr₁, Option.bind_some]
      simp only [hv, hz]
      exact hreg
    · have hf : (aMachine.view (aMachine.pass l sa)).flagB (·.zf) = false := by
        rw [← hz]; exact hzf
      rw [Machine.runXLoop, if_neg (by rw [hf]; decide)]
      exact hmach

/-! ## 3. The zero-trip guard -/

/-- The machine's `jcc` with nibble `4` on a machine zero flag `z`: to its target when `z`
    holds, else to the next index. -/
theorem aMachine_step_je_flag (prog : List RInstr) (pc tgt : Nat) (sa : AState) (z : Bool)
    (hz : sa.flags.zf.getD false = z) (hj : prog[pc]? = some (.jcc 4 tgt)) :
    RInstrSemantics.step aMachine prog pc sa
      = some (RInstrSemantics.Next.go (if z then tgt else pc + 1) sa) := by
  have hf : (aMachine.view sa).flagB (·.zf) = z := hz
  simp only [RInstrSemantics.step, hj, condtOfNibble_four, Option.map_some, condB_e, hf]
  cases z <;> rfl

/-- The decoded layout of a zero-trip-guarded counted loop: the instructions `pre`, the
    guard `cmp ctr, 0` and `je` to the exit, the pass `l.body ++ [l.cmpInstr]`, the
    back-edge `jne` to the loop head, and the instructions `rest` from the exit index
    `pre.length + l.body.length + 4` on. -/
def guardedLayout (pre : List RInstr) (l : XLoop 64) (rest : List RInstr) : List RInstr :=
  pre ++ [.op l.cmpInstr, .jcc 4 (pre.length + l.body.length + 4)]
    ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 (pre.length + 2)] ++ rest

theorem guardedLayout_cmp (pre : List RInstr) (l : XLoop 64) (rest : List RInstr) :
    (guardedLayout pre l rest)[pre.length]? = some (.op l.cmpInstr) := by
  simp [guardedLayout, List.append_assoc]

theorem guardedLayout_je (pre : List RInstr) (l : XLoop 64) (rest : List RInstr) :
    (guardedLayout pre l rest)[pre.length + 1]?
      = some (.jcc 4 (pre.length + l.body.length + 4)) := by
  simp [guardedLayout, List.append_assoc]

/-- **The guarded loop, run.** Let the guard `CMP:64 ctr, #0` simulate the machine's
    `l.cmpInstr` from `E` to `G`, with `G` fixing the machine zero flag to the flag-machine
    flag, which holds exactly when `m = 0`, and giving `Inv 0` at any program counter; let
    the trips be as in `decLoop_trips`. From states related by `E`, the flag machine's
    guarded region runs to a state `b'` with the flag set, the machine runs the decoded
    layout from the guard to the exit index, and the two end states are related by
    `Inv m`. For `m = 0` both skip the loop. -/
theorem decLoop_guarded_run (ctr : String) (body : List LinstrRM) (l : XLoop 64)
    (top endL : LLabel) (m : Nat) (E G : AState → LstateM → Bool → Prop)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop)
    (hg : DecSim E G [cmpRI ctr (.imm 0)] [l.cmpInstr])
    (hgflag : ∀ sa b zf, G sa b zf → sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0))
    (hg0 : ∀ sa b zf pc, G sa b zf → Inv 0 sa (b.setLpc pc) zf)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf)
    (pre rest : List RInstr) (sa : AState) (b : LstateM) (zf : Bool) (hE : E sa b zf) :
    ∃ sa' b', runFB m (.guarded top endL ctr [.straight body]) b zf = some (b', true)
      ∧ Reaches aMachine (guardedLayout pre l rest) pre.length sa
          (pre.length + l.body.length + 4) sa'
      ∧ Inv m sa' b' true := by
  obtain ⟨b₂, z₂, hr, hG⟩ := hg sa b zf hE
  rw [runStraightF_singleton] at hr
  obtain ⟨v, hv, rfl, rfl⟩ := fstepF_cmpRI_imm_inv ctr 0 b zf b₂ z₂ hr
  obtain ⟨hzf, hm0⟩ := hgflag _ _ _ hG
  have hcmp : Reaches aMachine (guardedLayout pre l rest) pre.length sa (pre.length + 1)
      (aMachine.runBlock sa [l.cmpInstr]) :=
    .single (aMachine_step_op _ _ _ _ (guardedLayout_cmp pre l rest))
  cases m with
  | zero =>
    have hz : (v == BitVec.ofNat 64 0) = true := hm0.2 rfl
    refine ⟨aMachine.runBlock sa [l.cmpInstr],
      b.setLpc (b.lpc + (flatFL [.straight body]).length + 6), ?_, ?_, ?_⟩
    · rw [runFB_guarded, hv]
      simp only [show (v == 0#64) = true from hz, if_true]
    · refine hcmp.trans (.single ?_)
      rw [aMachine_step_je_flag _ _ _ _ _ hzf (guardedLayout_je pre l rest), hz, if_pos rfl]
    · have := hg0 _ _ _ (b.lpc + (flatFL [.straight body]).length + 6) hG
      rw [hz] at this
      exact this
  | succ k =>
    have hz : (v == BitVec.ofNat 64 0) = false := by
      cases h' : (v == BitVec.ofNat 64 0)
      · rfl
      · exact absurd (hm0.1 h') (by omega)
    have hI0 := hg0 _ _ _ (b.lpc + 3) hG
    rw [hz] at hI0
    obtain ⟨sa', bR, hreg, hmach, hInv⟩ := decLoop_trips ctr body l (b.lpc + 3) (k + 1) Inv Inv'
      hsim hflag hnext k 0 (by omega) _ _ _ hI0
    refine ⟨sa', bR.setLpc (b.lpc + (flatFL [.straight body]).length + 6), ?_, ?_, hInv _⟩
    · rw [runFB_guarded, hv]
      simp only [show (v == 0#64) = false from hz, Bool.false_eq_true, if_false]
      exact congrArg (Option.map _) hreg
    · have hje : Reaches aMachine (guardedLayout pre l rest) (pre.length + 1)
          (aMachine.runBlock sa [l.cmpInstr]) (pre.length + 2)
          (aMachine.runBlock sa [l.cmpInstr]) := by
        refine .single ?_
        rw [aMachine_step_je_flag _ _ _ _ _ hzf (guardedLayout_je pre l rest), hz]
        rfl
      have hloop := reaches_xloop aMachine
        (pre ++ [.op l.cmpInstr, .jcc 4 (pre.length + l.body.length + 4)]) l rest (k + 1) _ _
        hmach
      rw [show (pre ++ [RInstr.op l.cmpInstr,
          RInstr.jcc 4 (pre.length + l.body.length + 4)]).length = pre.length + 2 by simp,
        show pre.length + 2 + l.body.length + 2 = pre.length + l.body.length + 4 by omega]
        at hloop
      exact hcmp.trans (hje.trans hloop)

/-- **The guarded loop on both machines.** Under the hypotheses of `decLoop_guarded_run`,
    with the flag machine's guarded loop `guardedFlagLoopLinstrRM top endL ctr body` of an
    all-`Lopn` body at the program counter of `b` in `P` and its two labels resolving to
    their positions: the flag machine runs from `b` to `b'` in a fuel
    `n ≤ guardedLoopFuel body.length m`, the machine runs the decoded layout from the guard
    to the exit index, and the two end states are related by `Inv m`. -/
theorem decLoop_guarded_fuel (ctr : String) (body : List LinstrRM) (l : XLoop 64)
    (top endL : LLabel) (m : Nat) (E G : AState → LstateM → Bool → Prop)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop)
    (hg : DecSim E G [cmpRI ctr (.imm 0)] [l.cmpInstr])
    (hgflag : ∀ sa b zf, G sa b zf → sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0))
    (hg0 : ∀ sa b zf pc, G sa b zf → Inv 0 sa (b.setLpc pc) zf)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf)
    (P : LprogM) (hbody : ∀ i ∈ body, IsLopn i) (b : LstateM)
    (hpos : ∀ k, k < (guardedFlagLoopLinstrRM top endL ctr body).length →
      P.body[b.lpc + k]? = (guardedFlagLoopLinstrRM top endL ctr body)[k]?)
    (htop : findLabelMem top P.body = some (b.lpc + 2))
    (hend : findLabelMem endL P.body = some (b.lpc + body.length + 5))
    (pre rest : List RInstr) (sa : AState) (zf : Bool) (hE : E sa b zf) :
    ∃ sa' b' n, n ≤ guardedLoopFuel body.length m
      ∧ (∀ f, lsemFuelMemF P (n + f) { prog := { base := b, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b', lfn := P.lfn }, zf := true })
      ∧ Reaches aMachine (guardedLayout pre l rest) pre.length sa
          (pre.length + l.body.length + 4) sa'
      ∧ Inv m sa' b' true ∧ b'.lpc = b.lpc + body.length + 6 := by
  obtain ⟨sa', b', hrun, hreach, hInv⟩ := decLoop_guarded_run ctr body l top endL m E G Inv Inv'
    hg hgflag hg0 hsim hflag hnext pre rest sa b zf hE
  have hflat : flatFL [FBlock.guarded top endL ctr [.straight body]]
      = guardedFlagLoopLinstrRM top endL ctr body := by simp
  have hn := segFBlocks_fuel P m [.guarded top endL ctr [.straight body]] b zf b' true
    (by simpa using hbody) (by rw [hflat]; exact hpos) (by simpa using ⟨htop, hend⟩)
    (by rw [runFBsL_cons, hrun, Option.bind_some, runFBsL_nil])
  have hsteps : stepsFBsL m [.guarded top endL ctr [.straight body]] b zf
      = stepsFB m (.guarded top endL ctr [.straight body]) b zf := by
    rw [stepsFBsL_cons, hrun]
    simp only [stepsFBsL_nil, Nat.add_zero]
  refine ⟨sa', b', _, ?_, hn, hreach, hInv, ?_⟩
  · rw [hsteps]
    exact stepsFB_guarded_straight_le m top endL ctr body b zf
  · rw [runFB_lpc _ _ _ _ _ _ hrun, fflat_guarded, guardedFlagLoop_length]
    simp only [fflatFL_cons, fflat_straight, fflatFL_nil, List.append_nil]
    omega

/-- `decLoop_guarded_fuel` without the bound on the fuel. -/
theorem decLoop_guarded (ctr : String) (body : List LinstrRM) (l : XLoop 64)
    (top endL : LLabel) (m : Nat) (E G : AState → LstateM → Bool → Prop)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop)
    (hg : DecSim E G [cmpRI ctr (.imm 0)] [l.cmpInstr])
    (hgflag : ∀ sa b zf, G sa b zf → sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0))
    (hg0 : ∀ sa b zf pc, G sa b zf → Inv 0 sa (b.setLpc pc) zf)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf)
    (P : LprogM) (hbody : ∀ i ∈ body, IsLopn i) (b : LstateM)
    (hpos : ∀ k, k < (guardedFlagLoopLinstrRM top endL ctr body).length →
      P.body[b.lpc + k]? = (guardedFlagLoopLinstrRM top endL ctr body)[k]?)
    (htop : findLabelMem top P.body = some (b.lpc + 2))
    (hend : findLabelMem endL P.body = some (b.lpc + body.length + 5))
    (pre rest : List RInstr) (sa : AState) (zf : Bool) (hE : E sa b zf) :
    ∃ sa' b' n,
      (∀ f, lsemFuelMemF P (n + f) { prog := { base := b, lfn := P.lfn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b', lfn := P.lfn }, zf := true })
      ∧ Reaches aMachine (guardedLayout pre l rest) pre.length sa
          (pre.length + l.body.length + 4) sa'
      ∧ Inv m sa' b' true ∧ b'.lpc = b.lpc + body.length + 6 := by
  obtain ⟨sa', b', n, _, h⟩ := decLoop_guarded_fuel ctr body l top endL m E G Inv Inv' hg hgflag
    hg0 hsim hflag hnext P hbody b hpos htop hend pre rest sa zf hE
  exact ⟨sa', b', n, h⟩

/-! ## 4. The flag machine is deterministic -/

/-- Two terminating runs of the flag machine from one state end in one state. -/
theorem lsemFuelMemF_det (P : LprogM) :
    ∀ (k k' : Nat) (s t t' : LstateMF), lsemFuelMemF P k s = some t →
      lsemFuelMemF P k' s = some t' → t = t' := by
  intro k
  induction k with
  | zero =>
    intro k' s t t' h h'
    cases hf : findInstrMem P s.prog with
    | none =>
      rw [lsemFuelMemF_halt P _ s hf] at h h'
      exact (Option.some.inj h).symm.trans (Option.some.inj h')
    | some i => simp [lsemFuelMemF, hf] at h
  | succ k ih =>
    intro k' s t t' h h'
    cases hf : findInstrMem P s.prog with
    | none =>
      rw [lsemFuelMemF_halt P _ s hf] at h h'
      exact (Option.some.inj h).symm.trans (Option.some.inj h')
    | some i =>
      cases k' with
      | zero => simp [lsemFuelMemF, hf] at h'
      | succ k' =>
        cases he : evalInstrPMemF P i s with
        | none => simp [lsemFuelMemF, hf, he] at h
        | some s' =>
          rw [lsemFuelMemF_step P k i s s' hf he] at h
          rw [lsemFuelMemF_step P k' i s s' hf he] at h'
          exact ih k' s' t t' h h'

/-! ## 5. A node: a straight segment, the guarded loop, and the exit -/

/-- The decoded layout of a node: the machine block `pre`, the guarded loop of `l`, the
    machine block `post` and `ret`. -/
def nodeLayout (pre : List (JInstr 64)) (l : XLoop 64) (post : List (JInstr 64)) :
    List RInstr :=
  guardedLayout (pre.map .op) l (post.map .op ++ [.ret])

/-- The fuel bound of a node of `seedsLen` seed instructions followed by a zero-trip-guarded
    loop of `bodyLen` body instructions run for `m` trips. -/
def nodeFuel (seedsLen bodyLen m : Nat) : Nat := seedsLen + guardedLoopFuel bodyLen m

@[simp] theorem nodeFuel_eq (seedsLen bodyLen m : Nat) :
    nodeFuel seedsLen bodyLen m = seedsLen + (m * (bodyLen + 2) + 4) := rfl

theorem nodeFuel_mono (seedsLen bodyLen : Nat) {m m' : Nat} (h : m ≤ m') :
    nodeFuel seedsLen bodyLen m ≤ nodeFuel seedsLen bodyLen m' :=
  Nat.add_le_add_left (guardedLoopFuel_mono bodyLen h) seedsLen

/-- **A node on both machines, with its fuel.** The flag-machine node
    `seeds ++ guardedFlagLoopLinstrRM top endL ctr body` (all-`Lopn` seeds and body, the two
    labels at their positions) and the decoded `nodeLayout pre l post`: `seeds` simulates
    `pre` from `E₀` to `E`, the guard and the trips are as in `decLoop_guarded_run`, and
    `post` takes `Inv m` to `Q`. From states related by `E₀`, with the flag machine at
    program counter `0`, the machine halts from index `0` in a state `sa'`, the flag machine
    halts in `t` at every fuel from `nodeFuel seeds.length body.length m` on, and
    `Q sa' t.prog.base` holds. -/
theorem decNode_halts_fuel (fn : String) (seeds body : List LinstrRM) (top endL : LLabel)
    (ctr : String) (l : XLoop 64) (m : Nat) (E₀ E G : AState → LstateM → Bool → Prop)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop) (Q : AState → LstateM → Prop)
    (pre post : List (JInstr 64))
    (hseeds : ∀ i ∈ seeds, IsLopn i) (hbody : ∀ i ∈ body, IsLopn i)
    (htop : findLabelMem top (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + 2))
    (hend : findLabelMem endL (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + body.length + 5))
    (hpre : DecSim E₀ E seeds pre)
    (hg : DecSim E G [cmpRI ctr (.imm 0)] [l.cmpInstr])
    (hgflag : ∀ sa b zf, G sa b zf → sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0))
    (hg0 : ∀ sa b zf pc, G sa b zf → Inv 0 sa (b.setLpc pc) zf)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf)
    (hpost : ∀ sa b, Inv m sa b true → Q (aMachine.runBlock sa post) b)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hE : E₀ sa b zf) :
    ∃ sa' t, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ (∀ k, nodeFuel seeds.length body.length m ≤ k →
          lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body))
            k { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ Q sa' t.prog.base := by
  set node := seeds ++ guardedFlagLoopLinstrRM top endL ctr body with hnode
  set P := singletonProgM fn node with hP
  have hfn : fn = P.lfn := rfl
  have hbodyP : P.body = node := rfl
  obtain ⟨b₁, z₁, hr₁, hE₁⟩ := hpre sa b zf hE
  have hlpc₁ : b₁.lpc = seeds.length := by
    rw [runStraightF_lpc seeds b zf b₁ z₁ hr₁, hpc, Nat.zero_add]
  have hseg := lsemFuelMemF_segF P fn hfn seeds b zf
  obtain ⟨sa', b', n, hnle, hn, hreach, hInv, hlpc'⟩ := decLoop_guarded_fuel ctr body l top
    endL m E G
    Inv Inv' hg hgflag hg0 hsim hflag hnext P hbody b₁
    (fun k hk => by
      rw [hbodyP, hlpc₁, hnode, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left])
    (by rw [hbodyP, hlpc₁]; exact htop) (by rw [hbodyP, hlpc₁]; exact hend)
    (pre.map .op) (post.map .op ++ [.ret]) (aMachine.runBlock sa pre) z₁ hE₁
  set pre₃ : List RInstr := pre.map .op ++ [.op l.cmpInstr,
      .jcc 4 ((pre.map RInstr.op).length + l.body.length + 4)]
    ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 ((pre.map RInstr.op).length + 2)] with hpre₃
  have e₃ : pre₃ ++ post.map .op ++ [.ret] = nodeLayout pre l post := by
    simp [hpre₃, nodeLayout, guardedLayout, List.append_assoc]
  have hlen₃ : pre₃.length = pre.length + l.body.length + 4 := by
    simp only [hpre₃, List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  refine ⟨aMachine.runBlock sa' post, { prog := { base := b', lfn := fn }, zf := true },
    halts_of_reaches (pc' := pre.length + l.body.length + 4 + post.length) ?_ ?_,
    fun k hk => ?_,
    hpost _ _ hInv⟩
  · have h₁ := reaches_ops aMachine [] pre
      ([.op l.cmpInstr, .jcc 4 ((pre.map RInstr.op).length + l.body.length + 4)]
        ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 ((pre.map RInstr.op).length + 2)]
        ++ (post.map .op ++ [.ret])) sa
    have e₁ : [] ++ pre.map RInstr.op
        ++ ([.op l.cmpInstr, .jcc 4 ((pre.map RInstr.op).length + l.body.length + 4)]
          ++ (l.body ++ [l.cmpInstr]).map .op ++ [.jcc 5 ((pre.map RInstr.op).length + 2)]
          ++ (post.map .op ++ [.ret])) = nodeLayout pre l post := by
      simp [nodeLayout, guardedLayout, List.append_assoc]
    rw [e₁, List.length_nil, Nat.zero_add] at h₁
    have h₃ := reaches_ops aMachine pre₃ post [.ret] sa'
    rw [e₃, hlen₃] at h₃
    rw [List.length_map] at hreach
    exact (h₁.trans hreach).trans h₃
  · rw [← e₃, ← hlen₃, List.getElem?_append_right (by simp)]
    simp
  · obtain ⟨f, rfl⟩ : ∃ f, k = seeds.length + (n + f) :=
      ⟨k - (seeds.length + n), by unfold nodeFuel at hk; omega⟩
    show lsemFuelMemF P (seeds.length + (n + f)) { prog := { base := b, lfn := fn }, zf := zf }
      = some { prog := { base := b', lfn := fn }, zf := true }
    rw [hseg (n + f) hseeds (fun k hk => by
      rw [hbodyP, hpc, Nat.zero_add, hnode, List.getElem?_append_left hk]), hr₁,
      Option.bind_some]
    refine (hn f).trans (lsemFuelMemF_halt P f _ ?_)
    show findInstrMem P ({ base := b', lfn := P.lfn } : LstatePM) = none
    rw [findInstrMemF_self, hbodyP, hlpc', hlpc₁]
    apply List.getElem?_eq_none
    simp only [hnode, List.length_append, guardedFlagLoop_length]
    omega

/-- **A node on both machines.** `decNode_halts_fuel` with the fuel of the flag-machine run
    existentially quantified. -/
theorem decNode_halts (fn : String) (seeds body : List LinstrRM) (top endL : LLabel)
    (ctr : String) (l : XLoop 64) (m : Nat) (E₀ E G : AState → LstateM → Bool → Prop)
    (Inv Inv' : Nat → AState → LstateM → Bool → Prop) (Q : AState → LstateM → Prop)
    (pre post : List (JInstr 64))
    (hseeds : ∀ i ∈ seeds, IsLopn i) (hbody : ∀ i ∈ body, IsLopn i)
    (htop : findLabelMem top (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + 2))
    (hend : findLabelMem endL (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)
      = some (seeds.length + body.length + 5))
    (hpre : DecSim E₀ E seeds pre)
    (hg : DecSim E G [cmpRI ctr (.imm 0)] [l.cmpInstr])
    (hgflag : ∀ sa b zf, G sa b zf → sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0))
    (hg0 : ∀ sa b zf pc, G sa b zf → Inv 0 sa (b.setLpc pc) zf)
    (hsim : ∀ t, t < m →
      DecSim (Inv t) (Inv' t) (body ++ [cmpRI ctr (.imm 0)]) (l.body ++ [l.cmpInstr]))
    (hflag : ∀ t, t < m → ∀ sa b zf, Inv' t sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m))
    (hnext : ∀ t, t < m → ∀ sa b zf pc, Inv' t sa b zf → Inv (t + 1) sa (b.setLpc pc) zf)
    (hpost : ∀ sa b, Inv m sa b true → Q (aMachine.runBlock sa post) b)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0) (hE : E₀ sa b zf) :
    ∃ sa' t k, Halts aMachine (nodeLayout pre l post) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (seeds ++ guardedFlagLoopLinstrRM top endL ctr body)) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ Q sa' t.prog.base := by
  obtain ⟨sa', t, hh, hrun, hQ⟩ := decNode_halts_fuel fn seeds body top endL ctr l m E₀ E G
    Inv Inv' Q pre post hseeds hbody htop hend hpre hg hgflag hg0 hsim hflag hnext hpost sa b
    zf hpc hE
  exact ⟨sa', t, _, hh, hrun _ (Nat.le_refl _), hQ⟩

/-! ## 6. The high half of the widening multiply, alone

`FheMontMulEmit.fuseMulHiLprog` keeps the low `MUL:64` in place and replaces the
`MULXHI:64` by a `mulx` whose low destination is a scratch register, so the two halves are
simulated separately: the low half by its own instruction, the high half by the `mulx`,
with any instructions in between. -/

variable {π : String → String} {L L' : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl : Prop}

theorem evalInstrA_mulx_regs (sa : AState) (H D S C r : String) :
    (evalInstrA sa (.mulx H D (.reg S) (.reg C))).regs r
      = if r = H then (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).2
        else if r = D then (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).1 else sa.regs r := rfl

theorem evalInstrA_loadMem_regs' (sa : AState) (D B : String) (off : Int) (r : String) :
    (evalInstrA sa (.loadMem D B off)).regs r
      = if r = D then read64 sa.mem (sa.regs B + BitVec.ofInt 64 off) else sa.regs r := by
  show (if r = D then _ else _) = _
  split <;> rfl

/-- **High half.** `MULXHI:64 hi, a, c` against `mulx %c, %D, %hi` whose implicit source
    `S` holds the value of `a` and whose low destination `D` holds no name live after. -/
theorem decSim_mulhi (hi a c S D : String) (ha : L a) (hc : L c)
    (hL : Survives π (fun r => L r ∧ π r ≠ D) L' hi) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ sa.regs S = sa.regs (π a))
      (DecLsemCorr π L' Lay frame K zl) [mulhiI hi a c] [.mulx (π hi) D (.reg S) (.reg (π c))] :=
  DecSim.single fun sa b zf ⟨h, hS⟩ =>
    ⟨_, zf, fstepF_mulhiI hi a c b zf _ _ (h.regs a ha) (h.regs c hc),
      (h.machWrite (L' := fun r => L r ∧ π r ≠ D) D
        (x86_MULX_lo_hi (sa.regs S) (sa.regs (π c))).1
        { sa with regs := fun r => if r = D then (x86_MULX_lo_hi (sa.regs S) (sa.regs (π c))).1
            else sa.regs r }
        (fun _ => rfl) rfl (fun r hr => hr) (fun hz => h.zfEq hz)).write hi _ _
        (fun r => by rw [evalInstrA_mulx_regs, hS]; rfl) rfl hL (fun hz => h.zfEq hz)⟩

/-- A store to an address whose eight bytes are disjoint from every cell of `K` and every
    frame slot, registers and flags unchanged, preserves the correspondence. -/
theorem DecLsemCorr.memWrite {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (X v : BitVec 64) (sa' : AState)
    (hregs : sa'.regs = sa.regs) (hflags : sa'.flags = sa.flags)
    (hmem : sa'.mem = write64 sa.mem X v)
    (hK : ∀ A j, K A j → Disjoint8 X (Lay.addr A j))
    (hF : ∀ q x, frame q = some x → Disjoint8 X x) :
    DecLsemCorr π L Lay frame K zl sa' b zf where
  regs r hr := by rw [hregs]; exact h.regs r hr
  zfEq hz := by rw [hflags]; exact h.zfEq hz
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [hmem, read64_write64_of_disjoint _ _ _ _ (hK A j hk)]; exact hr⟩
  slots A q hq := by
    obtain ⟨x, hx, hpx⟩ := h.slots A q hq
    exact ⟨x, hx, by rw [hmem, read64_write64_of_disjoint _ _ _ _ (hF q x hx)]; exact hpx⟩

/-- **High half with a saved low destination.** `MULXHI:64 hi, a, c` against the save of
    `D` to the word at `off(%SP)`, `mulx %c, %D, %hi` with implicit source `S` holding the
    value of `a`, and the reload of `D`. The saved word is disjoint from the cells of `K`
    and the frame slots, and `SP`, `D` and the register of `hi` are distinct. -/
theorem decSim_mulhi_saved (hi a c S D SP : String) (off : Int) (ha : L a) (hc : L c)
    (hSPD : SP ≠ D) (hSPh : SP ≠ π hi) (hDh : D ≠ π hi) (hL : Survives π L L' hi) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ sa.regs S = sa.regs (π a)
        ∧ (∀ A j, K A j → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) (Lay.addr A j))
        ∧ (∀ q x, frame q = some x → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) x))
      (DecLsemCorr π L' Lay frame K zl) [mulhiI hi a c]
      [.storeMem SP off (.reg D), .mulx (π hi) D (.reg S) (.reg (π c)), .loadMem D SP off] := by
  intro sa b zf ⟨h, hS, hK, hF⟩
  have hc1 := DecLsemCorr.memWrite h (sa.regs SP + BitVec.ofInt 64 off) (sa.regs D)
    (evalInstrA sa (.storeMem SP off (.reg D))) rfl rfl rfl hK hF
  refine ⟨_, zf, by
    rw [runStraightF_singleton]; exact fstepF_mulhiI hi a c b zf _ _ (h.regs a ha) (h.regs c hc),
    hc1.write hi _ _ (fun r => ?_) rfl hL (fun hz => h.zfEq hz)⟩
  set s₂ := evalInstrA (evalInstrA sa (.storeMem SP off (.reg D)))
    (.mulx (π hi) D (.reg S) (.reg (π c)))
  have e₂ : ∀ r, s₂.regs r = if r = π hi then (x86_MULX_lo_hi (sa.regs S) (sa.regs (π c))).2
      else if r = D then (x86_MULX_lo_hi (sa.regs S) (sa.regs (π c))).1 else sa.regs r :=
    fun r => evalInstrA_mulx_regs _ _ _ _ _ r
  have hm₂ : s₂.mem = write64 sa.mem (sa.regs SP + BitVec.ofInt 64 off) (sa.regs D) := rfl
  have hsp : s₂.regs SP = sa.regs SP := by rw [e₂, if_neg hSPh, if_neg hSPD]
  show (evalInstrA s₂ (.loadMem D SP off)).regs r = _
  rw [evalInstrA_loadMem_regs']
  by_cases hrD : r = D
  · subst hrD
    rw [if_pos rfl, hm₂, hsp, read64_write64_same, if_neg hDh]
    rfl
  · rw [if_neg hrD, e₂, if_neg hrD, hS]
    rfl

/-- **High half, pinned and saved.** `MULXHI:64 hi, a, c` against the fused site of
    `fuseMulHiLprog`: the pin `mov %a, %S` of the implicit source into a register `S` that
    holds no name live after, then `decSim_mulhi_saved`. -/
theorem decSim_mulhi_pinned (hi a c S D SP : String) (off : Int) (ha : L a) (hc : L c)
    (haS : π a ≠ S) (hcS : π c ≠ S) (hSSP : S ≠ SP)
    (hSPD : SP ≠ D) (hSPh : SP ≠ π hi) (hDh : D ≠ π hi)
    (hL : Survives π (fun r => L r ∧ π r ≠ S) L' hi) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
        ∧ (∀ A j, K A j → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) (Lay.addr A j))
        ∧ (∀ q x, frame q = some x → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) x))
      (DecLsemCorr π L' Lay frame K zl) [mulhiI hi a c]
      [.mov S (.reg (π a)), .storeMem SP off (.reg D), .mulx (π hi) D (.reg S) (.reg (π c)),
        .loadMem D SP off] := by
  have e : ∀ (sa : AState) x, (evalInstrA sa (.mov S (.reg (π a)))).regs x
      = if x = S then sa.regs (π a) else sa.regs x := fun _ _ => rfl
  have h₁ : DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
        ∧ (∀ A j, K A j → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) (Lay.addr A j))
        ∧ (∀ q x, frame q = some x → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) x))
      (fun sa b zf => DecLsemCorr π (fun r => L r ∧ π r ≠ S) Lay frame K zl sa b zf
        ∧ sa.regs S = sa.regs (π a)
        ∧ (∀ A j, K A j → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) (Lay.addr A j))
        ∧ (∀ q x, frame q = some x → Disjoint8 (sa.regs SP + BitVec.ofInt 64 off) x))
      [] [.mov S (.reg (π a))] :=
    DecSim.machOnly fun sa b zf ⟨h, hK, hF⟩ =>
      ⟨h.machWrite S _ _ (fun _ => rfl) rfl (fun r hr => hr) (fun hz => h.zfEq hz),
        by rw [e, e, if_pos rfl, if_neg haS],
        by rw [e, if_neg (Ne.symm hSSP)]; exact hK,
        by rw [e, if_neg (Ne.symm hSSP)]; exact hF⟩
  exact DecSim.append h₁ (decSim_mulhi_saved hi a c S D SP off ⟨ha, haS⟩ ⟨hc, hcS⟩ hSPD hSPh
    hDh hL)

/-! ## 7. Three-address operations through a copy -/

/-- **Two-source operation through a copy.** A three-address `opn d, a, c` as in
    `decSim_binReg`, against the copy `mov %a, %d` followed by the two-address machine
    instruction `mk` on the register of `d` and the register of `c`, which differ. -/
theorem decSim_binReg_mov (opn base : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    (d a c : String) (ha : L a) (hc : L c) (hdc : π c ≠ π d) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [binRegI opn d a c] [.mov (π d) (.reg (π a)), mk (π d) (.reg (π c))] := by
  intro sa b zf h
  refine ⟨_, zf, ?_, DecLsemCorr.withALUFlags (h.write d (f (sa.regs (π a)) (sa.regs (π c)))
    (aMachine.runBlock sa [.mov (π d) (.reg (π a)), mk (π d) (.reg (π c))]) (fun r => ?_)
    (hmkm _ _ _) hL (fun hz : False => hz.elim)) (binRegI opn d a c) b⟩
  · rw [runStraightF_singleton, fstepF_binRegI opn base d a c hstrip hcmp hmul hcarry
      (ne_mov_of_applyOpnN hf) b zf _ (h.regs a ha), h.regs c hc, Option.bind_some, hf,
      Option.map_some]
  · show (evalInstrA (evalInstrA sa (.mov (π d) (.reg (π a)))) (mk (π d) (.reg (π c)))).regs r
      = _
    rw [hmk]
    have e : ∀ x, (evalInstrA sa (.mov (π d) (.reg (π a)))).regs x
        = if x = π d then sa.regs (π a) else sa.regs x := fun _ => rfl
    rw [e, e, if_pos rfl, if_neg hdc, e]
    split <;> rfl

/-- `MUL:64 d, a, c` against `mov %a, %d` and `imul %c, %d`, the registers of `c` and `d`
    distinct. -/
theorem decSim_imul_mov (d a c : String) (ha : L a) (hc : L c) (hdc : π c ≠ π d)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [binRegI "MUL:64" d a c] [.mov (π d) (.reg (π a)), .imul (π d) (.reg (π c))] :=
  decSim_binReg_mov _ "MUL" stripWidthTag_MUL64 (by decide +kernel)
    (by decide) (by decide) (· * ·) (fun _ _ => rfl) JInstr.imul (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hdc hL

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
