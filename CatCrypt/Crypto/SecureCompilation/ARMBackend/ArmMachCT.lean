/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the `mpn_and_n` body at the AArch64 machine

The bytes `armAndBytes` of the `mpn_and_n` body followed by `RET` are run at the machine
`armMach r` by `ArmBytesRun r`: the bytes decode to a program, and the program has a halting
run with leakage `IsaMachine.RunL` from index 0. A run of an `IsaMachine` is determined by
its start index and start state (`runL_det`), because the action at an index is a function
of the state; so the trace of `ArmBytesRun r armAndBytes` from a state `b` is the block
leakage of `armAndCode` from `b` (`armBytesRun_and_iff`).

Under `ArmRegime.dit` that trace is `armAndTrace b`, the addresses of the two limb loads and
of the limb store, computed from the array bases `x1`, `x0`, `x3` and the index `x4`. The
public agreement `ArmAndPub` relates two machine states that agree on these four registers;
the limbs in memory, the count `x2`, the scratch registers and the flags are unconstrained.

The statements under `ArmRegime.dit` hold for a core that runs with `PSTATE.DIT = 1` and
meets the table `CT.ArmMnem.leaksOperands`. That table classes `MOVZ` as data-independent
although the FEAT_DIT list names `MOVK` only (`CT.ArmMnem.isDIT_not_listed_iff`); `armAndCode`
holds two `LDR`, one `AND`, one `STR`, one `ADD` and one `SUB`, and no `MOVZ`
(`armAndCode_no_movz`), so the statements here do not use that classification.

## Main definitions

* `armAndBytes`, `ArmBytesRun`: the bytes of the body with `RET`, and their machine run with
  leakage.
* `ArmAndPub`, `armAndTrace`: the public agreement of two machine states, and the trace of
  the body as a function of the public registers.

## Main results

* `runL_det`: a run with leakage of an `IsaMachine` has one trace and one final state.
* `armBytesRun_and_iff`: the trace of the bytes is the block leakage of `armAndCode`.
* `mpn_and_n_armMach_ct`: under `ArmRegime.dit` the machine run of the bytes is
  `ConstantTimeRel` for `ArmAndPub`.
* `mpn_and_n_armMach_run_ct`: the value conclusion of `arm_and_mach` joined with the trace
  `armAndTrace` and its independence of the data outside `ArmAndPub`.
* `armAndCode_leak_unguaranteed_data`, `mpn_and_n_armMach_not_ct_unguaranteed`: under
  `ArmRegime.unguaranteed` the trace holds the loaded limb, and the run is not
  `ConstantTimeRel` for `ArmAndPub`.
-/

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## Determinism of a run with leakage -/

/-- **A run with leakage has one trace and one final state**: two runs of the same program
    from the same index and state, under any two side conditions, have equal traces and equal
    final states. -/
theorem runL_det {M : IsaMachine} {ok ok' : M.MState → M.Op → Prop} {prog : List M.Instr}
    {pc : Nat} {s : M.MState} {t₁ t₂ : List CTLeak} {s₁ s₂ : M.MState}
    (h₁ : M.RunL ok prog pc s t₁ s₁) (h₂ : M.RunL ok' prog pc s t₂ s₂) :
    t₁ = t₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing t₂ s₂ with
  | ret h =>
    cases h₂ with
    | ret _ => exact ⟨rfl, rfl⟩
    | _ => simp_all
  | op h _ _ ih =>
    cases h₂ with
    | op h' _ hr' =>
      rw [h] at h'
      cases h'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | _ => simp_all
  | block h _ _ ih =>
    cases h₂ with
    | block h' _ hr' =>
      rw [h] at h'
      cases h'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | _ => simp_all
  | branch h _ ih =>
    cases h₂ with
    | branch h' hr' =>
      rw [h] at h'
      cases h'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩
    | _ => simp_all
  | call h _ _ _ _ ihc ihr =>
    cases h₂ with
    | call h' _ hc' _ hr' =>
      rw [h] at h'
      cases h'
      obtain ⟨rfl, rfl⟩ := ihc hc'
      obtain ⟨rfl, rfl⟩ := ihr hr'
      exact ⟨rfl, rfl⟩
    | _ => simp_all

/-! ## The bytes of the body and their run -/

/-- The bytes of the `mpn_and_n` body followed by the bytes of `RET`. -/
def armAndBytes : List (BitVec 8) :=
  encodeBMBlock armAlloc armAndCode ++ ArmAbiEncoder.encRet

/-- **The machine run of a byte string** under the regime `r`: the bytes decode to a program
    that has a halting run from index 0 and state `b` with leakage trace `t`. -/
def ArmBytesRun (r : ArmRegime) (bytes : List (BitVec 8)) (b : BMState) (t : List CTLeak) :
    Prop :=
  ∃ prog b', (armMach r).decode bytes = some prog ∧
    (armMach r).RunL (fun _ _ => True) prog 0 b t b'

/-- The bytes of the body decode to `armAndCode` followed by `RET`. -/
theorem armAndBytes_decode (r : ArmRegime) :
    (armMach r).decode armAndBytes = some (armAndCode.map .op ++ [.ret]) := by
  have hb : decodeBMBlock (encodeBMBlock armAlloc armAndCode) = some armAndCode :=
    armSelM_decodeBlock (armAndBody 0) armAndCode (armAndBody_sel 0)
  have hd := decodeArmProg_block ArmAbiEncoder.encRet [.ret] decodeArmProg_encRet
    (encodeBMBlock armAlloc armAndCode) armAndCode hb
  rw [armMach_decode, armAndBytes]
  exact hd

/-- **The trace of the bytes of the body is the block leakage of `armAndCode`**, under every
    regime and from every state. -/
theorem armBytesRun_and_iff (r : ArmRegime) (b : BMState) (t : List CTLeak) :
    ArmBytesRun r armAndBytes b t ↔ t = (armMach r).blockLeak b armAndCode := by
  constructor
  · rintro ⟨prog, b', hdec, hrun⟩
    rw [armAndBytes_decode] at hdec
    cases hdec
    exact (runL_det hrun (armMach_runL_block r armAndCode armAndCode_straight b)).1
  · rintro rfl
    exact ⟨_, _, armAndBytes_decode r, armMach_runL_block r armAndCode armAndCode_straight b⟩

/-! ## The public data and the trace -/

/-- **The public agreement of two machine states** for the `mpn_and_n` body: equal array
    bases `x0`, `x1`, `x3` and equal index `x4`. -/
def ArmAndPub (b₁ b₂ : BMState) : Prop :=
  b₁.regs.get "x0" = b₂.regs.get "x0" ∧ b₁.regs.get "x1" = b₂.regs.get "x1" ∧
    b₁.regs.get "x3" = b₂.regs.get "x3" ∧ b₁.regs.get "x4" = b₂.regs.get "x4"

/-- The trace of the body under `PSTATE.DIT = 1`: the addresses of the two limb loads and of
    the limb store. -/
def armAndTrace (b : BMState) : List CTLeak :=
  [ .addr "" ((b.regs.get "x1" + (b.regs.get "x4" <<< 3)).toNat : Int)
  , .addr "" ((b.regs.get "x0" + (b.regs.get "x4" <<< 3)).toNat : Int)
  , .addr "" ((b.regs.get "x3" + (b.regs.get "x4" <<< 3)).toNat : Int) ]

/-- States that agree on the public registers have the same `armAndTrace`. -/
theorem armAndTrace_congr {b₁ b₂ : BMState} (h : ArmAndPub b₁ b₂) :
    armAndTrace b₁ = armAndTrace b₂ := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  simp only [armAndTrace, h0, h1, h3, h4]

/-- No instruction of `armAndCode` is `MOVZ`. -/
theorem armAndCode_no_movz : ∀ bi ∈ armAndCode, bmMnem bi ≠ .movz := by
  decide

/-! ## Constant time under `PSTATE.DIT = 1` -/

/-- **The `mpn_and_n` bytes are constant time at the AArch64 machine under `PSTATE.DIT = 1`.**
    Two machine runs of `armAndBytes` from states that agree on the array bases `x0`, `x1`,
    `x3` and on the index `x4` have equal leakage traces.

    The statement holds under the regime constructor `ArmRegime.dit`: a core that runs with
    `PSTATE.DIT = 1` and meets the table `CT.ArmMnem.leaksOperands`. The table classes `MOVZ`
    as data-independent although the FEAT_DIT list names `MOVK` only; the code holds no
    `MOVZ` (`armAndCode_no_movz`). The address of a load or store is an event under every
    regime, and is equal in the two runs because it is computed from the public registers. -/
theorem mpn_and_n_armMach_ct :
    ConstantTimeRel ArmAndPub (ArmBytesRun .dit armAndBytes) := by
  intro b₁ b₂ t₁ t₂ hp h₁ h₂
  rw [armBytesRun_and_iff, armAndCode_leak_dit] at h₁ h₂
  rw [h₁, h₂]
  exact armAndTrace_congr hp

/-- The functional form of `mpn_and_n_armMach_ct`: the trace function `armAndTrace` is
    `ConstantTime` for `ArmAndPub`, and it is the trace of the machine run. -/
theorem mpn_and_n_armMach_ct_fun :
    ConstantTime ArmAndPub armAndTrace ∧
      ∀ b t, ArmBytesRun .dit armAndBytes b t ↔ t = armAndTrace b :=
  ⟨fun _ _ hp => armAndTrace_congr hp, fun b t => by
    rw [armBytesRun_and_iff, armAndCode_leak_dit]; rfl⟩

/-- **The `mpn_and_n` body at `armMach .dit`: value and trace.** From an `LstateMF` related
    to a machine state `b` on `armRegs` and on the arrays `x0`, `x1`, `x3` of `n` limbs, laid
    out separately, with the index `x4` below `n`: the `armIsa` run of the body succeeds; the
    bytes `armAndBytes` decode to a program whose machine run from `b` halts in a state
    related to the `armIsa` result, with the trace `armAndTrace b`; and every machine run of
    the bytes from a state that agrees with `b` on `ArmAndPub` has the same trace.

    The trace conjuncts hold under the regime constructor `ArmRegime.dit`, as stated at
    `mpn_and_n_armMach_ct`. -/
theorem mpn_and_n_armMach_run_ct (P : LprogM) (n : Nat) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel armAndArrs (fun _ => n) s b)
    (hsep : ArmArrsSep armAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "x4").toNat < n) :
    ∃ s' b', armIsa.runL P (armAndBody n) s = some s'
      ∧ (armMach .dit).decode armAndBytes = some (armAndCode.map .op ++ [.ret])
      ∧ (armMach .dit).RunL (fun _ _ => True) (armAndCode.map .op ++ [.ret]) 0 b
          (armAndTrace b) b'
      ∧ RegRel armRegs s' b'.regs.get ∧ ArmMemRel armAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s'
      ∧ ∀ b₂ t₂, ArmAndPub b b₂ → ArmBytesRun .dit armAndBytes b₂ t₂ → t₂ = armAndTrace b := by
  obtain ⟨hdec, s', b', hs', -, hl, h1, h2, h3⟩ := arm_and_mach .dit P n s b hrel hmem hsep hidx
  rw [armAndCode_leak_dit] at hl
  refine ⟨s', b', hs', hdec, hl, h1, h2, h3, ?_⟩
  intro b₂ t₂ hp h₂
  exact (mpn_and_n_armMach_ct b b₂ _ t₂ hp
    ((mpn_and_n_armMach_ct_fun.2 b _).mpr rfl) h₂).symm

/-! ## Without a timing guarantee -/

/-- **Under `ArmRegime.unguaranteed` the trace of the body holds the loaded limb**: its
    second event is the operand event of the first load, with the limb read at the address
    `x1 + 8·x4`. -/
theorem armAndCode_leak_unguaranteed_data (b : BMState) :
    ((armMach .unguaranteed).blockLeak b armAndCode)[1]? =
      some (.vtCall ("a64." ++ reprStr ArmMnem.ldr)
        [[(b.regs.get "x1").toNat, (b.regs.get "x4").toNat,
          (read64 b.mem (b.regs.get "x1" + (b.regs.get "x4" <<< 3))).toNat]]) := by
  simp [armAndCode, IsaMachine.blockLeak, armOpLeak, bmAddrLeak, bmAddr?, armAddrR, bmMnem,
    bmDataArgs, ArmRegime.leaksOperands, ArmMnem.isControl]

/-- The machine state with every register `0`, clear flags and every memory byte `v`. -/
def armConstMem (v : BitVec 8) : BMState :=
  { regs := { regs := fun _ => 0, cf := false }, zf := false, mem := fun _ => v, pc := 0 }

/-- **Without a timing guarantee the `mpn_and_n` bytes are not constant time**: the states
    `armConstMem 0` and `armConstMem 1` agree on every register and differ in the limbs, and
    their runs under `ArmRegime.unguaranteed` have different traces. -/
theorem mpn_and_n_armMach_not_ct_unguaranteed :
    ¬ ConstantTimeRel ArmAndPub (ArmBytesRun .unguaranteed armAndBytes) := by
  intro h
  have he := h (armConstMem 0) (armConstMem 1) _ _ ⟨rfl, rfl, rfl, rfl⟩
    ((armBytesRun_and_iff _ _ _).mpr rfl) ((armBytesRun_and_iff _ _ _).mpr rfl)
  have h1 := congrArg (fun t => t[1]?) he
  simp only [armAndCode_leak_unguaranteed_data] at h1
  revert h1
  simp [armConstMem, read64]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach
