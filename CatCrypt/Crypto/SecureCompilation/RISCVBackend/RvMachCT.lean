/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the `mpn_and_n` body at the RV64 machine

The bytes `rvAndBytes` of the `mpn_and_n` body followed by `ret` are run at the machine
`rvMach r` by `RvBytesRun r`: the bytes decode to a program, and the program has a halting
run with leakage `IsaMachine.RunL` from index 0. A run of an `IsaMachine` is determined by
its start index and start state (`runL_det`), because the action at an index is a function
of the state; so the trace of `RvBytesRun r rvAndBytes` from a state `b` is the block leakage
of `rvAndCode.flatten` from `b` (`rvBytesRun_and_iff`).

Under `RvRegime.zktMemData` that trace is `rvAndTrace b`, the addresses of the two limb loads
and of the limb store, computed from the array bases `a1`, `a0`, `a3` and the index `a4`. The
public agreement `RvAndPub` relates two machine states that agree on these four registers;
the limbs in memory, the count `a2` and the scratch registers are unconstrained.

The regime `RvRegime.zktMemData` is Zkt with the assumption that the latency of a load or
store is independent of the value transferred. The assumption is beyond the ratified Zkt
text, which excludes loads and stores. Under the regime `RvRegime.zkt` of the ratified text
the trace holds the loaded limb (`rvAndCode_leak_zkt_data`) and the run is not constant time
for `RvAndPub` (`mpn_and_n_rvMach_not_ct_zkt`); the same holds under `RvRegime.unguaranteed`.

## Main definitions

* `rvAndBytes`, `RvBytesRun`: the bytes of the body with `ret`, and their machine run with
  leakage.
* `RvAndPub`, `rvAndTrace`: the public agreement of two machine states, and the trace of the
  body as a function of the public registers.

## Main results

* `runL_det`: a run with leakage of an `IsaMachine` has one trace and one final state.
* `rvBytesRun_and_iff`: the trace of the bytes is the block leakage of `rvAndCode.flatten`.
* `mpn_and_n_rvMach_ct`: under `RvRegime.zktMemData` the machine run of the bytes is
  `ConstantTimeRel` for `RvAndPub`.
* `mpn_and_n_rvMach_run_ct`: the value conclusion of `rv_and_mach` joined with the trace
  `rvAndTrace` and its independence of the data outside `RvAndPub`.
* `rvAndCode_leak_zkt_data`, `mpn_and_n_rvMach_not_ct_zkt`: under `RvRegime.zkt` the trace
  holds the loaded limb, and the run is not `ConstantTimeRel` for `RvAndPub`.
* `rvAndCode_leak_unguaranteed_data`, `mpn_and_n_rvMach_not_ct_unguaranteed`: the same under
  `RvRegime.unguaranteed`.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
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

/-- The bytes of the `mpn_and_n` body followed by the bytes of `ret`. -/
def rvAndBytes : List (BitVec 8) :=
  encodeRMBlock64 rvAndCode.flatten ++ wordLE RiscvElfObject.encRet

/-- **The machine run of a byte string** under the regime `r`: the bytes decode to a program
    that has a halting run from index 0 and state `b` with leakage trace `t`. -/
def RvBytesRun (r : RvRegime) (bytes : List (BitVec 8)) (b : RMState64) (t : List CTLeak) :
    Prop :=
  ∃ prog b', (rvMach r).decode bytes = some prog ∧
    (rvMach r).RunL (fun _ _ => True) prog 0 b t b'

/-- The instructions of the `mpn_and_n` body are straight-line. -/
theorem rvAndCode_straight : ∀ bi ∈ rvAndCode.flatten, rmStraight bi = true :=
  rvSelM_straight_block (rvAndBody 0) rvAndCode (rvAndBody_sel 0)

/-- The bytes of the body decode to `rvAndCode.flatten` followed by `ret`. -/
theorem rvAndBytes_decode (r : RvRegime) :
    (rvMach r).decode rvAndBytes = some (rvAndCode.flatten.map .op ++ [.ret]) := by
  have hb : decodeRMBlock64 (encodeRMBlock64 rvAndCode.flatten) = some rvAndCode.flatten :=
    decodeRMBlock64_encode _
      (rvSelM_roundTrip_block (rvAndBody 0) rvAndCode (rvAndBody_sel 0))
  have hd := decodeRvProg_block (wordLE RiscvElfObject.encRet) [.ret] decodeRvProg_encRet
    (encodeRMBlock64 rvAndCode.flatten) rvAndCode.flatten hb
  rw [rvMach_decode, rvAndBytes]
  exact hd

/-- **The trace of the bytes of the body is the block leakage of `rvAndCode.flatten`**, under
    every regime and from every state. -/
theorem rvBytesRun_and_iff (r : RvRegime) (b : RMState64) (t : List CTLeak) :
    RvBytesRun r rvAndBytes b t ↔ t = (rvMach r).blockLeak b rvAndCode.flatten := by
  constructor
  · rintro ⟨prog, b', hdec, hrun⟩
    rw [rvAndBytes_decode] at hdec
    cases hdec
    exact (runL_det hrun (rvMach_runL_block r rvAndCode.flatten rvAndCode_straight b)).1
  · rintro rfl
    exact ⟨_, _, rvAndBytes_decode r,
      rvMach_runL_block r rvAndCode.flatten rvAndCode_straight b⟩

/-! ## The public data and the trace -/

/-- **The public agreement of two machine states** for the `mpn_and_n` body: equal array
    bases `a0`, `a1`, `a3` and equal index `a4`. -/
def RvAndPub (b₁ b₂ : RMState64) : Prop :=
  b₁.regs.get "a0" = b₂.regs.get "a0" ∧ b₁.regs.get "a1" = b₂.regs.get "a1" ∧
    b₁.regs.get "a3" = b₂.regs.get "a3" ∧ b₁.regs.get "a4" = b₂.regs.get "a4"

/-- The trace of the body under `RvRegime.zktMemData`: the addresses of the two limb loads
    and of the limb store. -/
def rvAndTrace (b : RMState64) : List CTLeak :=
  [ .addr "" ((b.regs.get "a1" + (b.regs.get "a4" <<< 3)).toNat : Int)
  , .addr "" ((b.regs.get "a0" + (b.regs.get "a4" <<< 3)).toNat : Int)
  , .addr "" ((b.regs.get "a3" + (b.regs.get "a4" <<< 3)).toNat : Int) ]

/-- States that agree on the public registers have the same `rvAndTrace`. -/
theorem rvAndTrace_congr {b₁ b₂ : RMState64} (h : RvAndPub b₁ b₂) :
    rvAndTrace b₁ = rvAndTrace b₂ := by
  obtain ⟨h0, h1, h3, h4⟩ := h
  simp only [rvAndTrace, h0, h1, h3, h4]

/-! ## Constant time under `RvRegime.zktMemData` -/

/-- **The `mpn_and_n` bytes are constant time at the RV64 machine under
    `RvRegime.zktMemData`.** Two machine runs of `rvAndBytes` from states that agree on the
    array bases `a0`, `a1`, `a3` and on the index `a4` have equal leakage traces.

    The statement holds under the regime constructor `RvRegime.zktMemData`: an implementation
    of Zkt on which the latency of a load or store is independent of the value transferred.
    That assumption is beyond the ratified Zkt text, which excludes loads, stores and
    conditional branches; it is to be established for the implementation separately, and
    `mpn_and_n_rvMach_not_ct_zkt` is the statement without it. The address of a load or
    store is an event under every regime, and is equal in the two runs because it is computed
    from the public registers. -/
theorem mpn_and_n_rvMach_ct :
    ConstantTimeRel RvAndPub (RvBytesRun .zktMemData rvAndBytes) := by
  intro b₁ b₂ t₁ t₂ hp h₁ h₂
  rw [rvBytesRun_and_iff, rvAndCode_leak_zktMemData] at h₁ h₂
  rw [h₁, h₂]
  exact rvAndTrace_congr hp

/-- The functional form of `mpn_and_n_rvMach_ct`: the trace function `rvAndTrace` is
    `ConstantTime` for `RvAndPub`, and it is the trace of the machine run. -/
theorem mpn_and_n_rvMach_ct_fun :
    ConstantTime RvAndPub rvAndTrace ∧
      ∀ b t, RvBytesRun .zktMemData rvAndBytes b t ↔ t = rvAndTrace b :=
  ⟨fun _ _ hp => rvAndTrace_congr hp, fun b t => by
    rw [rvBytesRun_and_iff, rvAndCode_leak_zktMemData]; rfl⟩

/-- **The `mpn_and_n` body at `rvMach .zktMemData`: value and trace.** From an `LstateMF`
    related to a machine state `b` on `rvMemRegs` and on the arrays `a0`, `a1`, `a3` of `n`
    limbs, laid out separately, with the index `a4` below `n`: the `rvIsa` run of the body
    succeeds; the bytes `rvAndBytes` decode to a program whose machine run from `b` halts in
    a state related to the `rvIsa` result, with the trace `rvAndTrace b`; and every machine
    run of the bytes from a state that agrees with `b` on `RvAndPub` has the same trace.

    The trace conjuncts hold under the regime constructor `RvRegime.zktMemData`, whose
    assumption on loads and stores is beyond the ratified Zkt text, as stated at
    `mpn_and_n_rvMach_ct`. -/
theorem mpn_and_n_rvMach_run_ct (P : LprogM) (n : Nat) (s : LstateMF) (b : RMState64)
    (hrel : RegRel rvMemRegs s b.regs.get) (hmem : RvMemRel rvAndArrs (fun _ => n) s b)
    (hsep : RvArrsSep rvAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "a4").toNat < n) :
    ∃ s' b', rvIsa.runL P (rvAndBody n) s = some s'
      ∧ (rvMach .zktMemData).decode rvAndBytes = some (rvAndCode.flatten.map .op ++ [.ret])
      ∧ (rvMach .zktMemData).RunL (fun _ _ => True) (rvAndCode.flatten.map .op ++ [.ret]) 0 b
          (rvAndTrace b) b'
      ∧ RegRel rvMemRegs s' b'.regs.get ∧ RvMemRel rvAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s'
      ∧ ∀ b₂ t₂, RvAndPub b b₂ → RvBytesRun .zktMemData rvAndBytes b₂ t₂ → t₂ = rvAndTrace b := by
  obtain ⟨hdec, s', b', hs', -, hl, h1, h2, h3⟩ :=
    rv_and_mach .zktMemData P n s b hrel hmem hsep hidx
  rw [rvAndCode_leak_zktMemData] at hl
  refine ⟨s', b', hs', hdec, hl, h1, h2, h3, ?_⟩
  intro b₂ t₂ hp h₂
  exact (mpn_and_n_rvMach_ct b b₂ _ t₂ hp
    ((mpn_and_n_rvMach_ct_fun.2 b _).mpr rfl) h₂).symm

/-! ## Under the ratified Zkt text, and without a timing guarantee -/

/-- The machine state with every register `0` and every memory byte `v`. -/
def rvConstMem (v : BitVec 8) : RMState64 :=
  { regs := { regs := fun _ => 0 }, mem := fun _ => v, pc := 0 }

/-- **Under `RvRegime.zkt` the trace of the body holds the loaded limb**: its second event is
    the operand event of the first load, with the limb read at the address `a1 + 8·a4`. -/
theorem rvAndCode_leak_zkt_data (b : RMState64) :
    ((rvMach .zkt).blockLeak b rvAndCode.flatten)[1]? =
      some (.vtCall "rv64.ld"
        [[(b.regs.get "a1" + (b.regs.get "a4" <<< 3)).toNat,
          (read64 b.mem (b.regs.get "a1" + (b.regs.get "a4" <<< 3))).toNat]]) := by
  simp [rvAndCode, rvIdxAddr, IsaMachine.blockLeak, rvOpLeak, RvRegime.leaksOperands,
    rmZktLeaks, RInst64.mnem_leaksOperands, show RvMnem.ld.leaksOperands = true from rfl,
    show RvMnem.sd.leaksOperands = true from rfl, rmAddrLeak, rmAddr?, rmName, rmDataArgs,
    rvAddr, evalRMInst64, evalRInst64, RState64.set, opAdd64]

/-- **Under the ratified Zkt text the `mpn_and_n` bytes are not constant time for
    `RvAndPub`**: the states `rvConstMem 0` and `rvConstMem 1` agree on every register and
    differ in the limbs, and their runs under `RvRegime.zkt` have different traces. The
    assumption of `RvRegime.zktMemData` is what `mpn_and_n_rvMach_ct` uses beyond Zkt. -/
theorem mpn_and_n_rvMach_not_ct_zkt :
    ¬ ConstantTimeRel RvAndPub (RvBytesRun .zkt rvAndBytes) := by
  intro h
  have he := h (rvConstMem 0) (rvConstMem 1) _ _ ⟨rfl, rfl, rfl, rfl⟩
    ((rvBytesRun_and_iff _ _ _).mpr rfl) ((rvBytesRun_and_iff _ _ _).mpr rfl)
  have h1 := congrArg (fun t => t[1]?) he
  simp only [rvAndCode_leak_zkt_data] at h1
  revert h1
  simp [rvConstMem, read64]

/-- **Under `RvRegime.unguaranteed` the trace of the body holds the loaded limb**: its fourth
    event is the operand event of the first load. -/
theorem rvAndCode_leak_unguaranteed_data (b : RMState64) :
    ((rvMach .unguaranteed).blockLeak b rvAndCode.flatten)[3]? =
      some (.vtCall "rv64.ld"
        [[(b.regs.get "a1" + (b.regs.get "a4" <<< 3)).toNat,
          (read64 b.mem (b.regs.get "a1" + (b.regs.get "a4" <<< 3))).toNat]]) := by
  simp [rvAndCode, rvIdxAddr, IsaMachine.blockLeak, rvOpLeak, RvRegime.leaksOperands,
    rmStraight, rmAddrLeak, rmAddr?, rmName, rmDataArgs, rvAddr, evalRMInst64, evalRInst64,
    RState64.set, opAdd64]

/-- **Without a timing guarantee the `mpn_and_n` bytes are not constant time**: the runs of
    `rvConstMem 0` and `rvConstMem 1` under `RvRegime.unguaranteed` have different traces. -/
theorem mpn_and_n_rvMach_not_ct_unguaranteed :
    ¬ ConstantTimeRel RvAndPub (RvBytesRun .unguaranteed rvAndBytes) := by
  intro h
  have he := h (rvConstMem 0) (rvConstMem 1) _ _ ⟨rfl, rfl, rfl, rfl⟩
    ((rvBytesRun_and_iff _ _ _).mpr rfl) ((rvBytesRun_and_iff _ _ _).mpr rfl)
  have h1 := congrArg (fun t => t[3]?) he
  simp only [rvAndCode_leak_unguaranteed_data] at h1
  revert h1
  simp [rvConstMem, read64]

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach
