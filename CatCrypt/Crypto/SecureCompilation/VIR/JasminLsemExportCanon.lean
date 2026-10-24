/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripLogical

@[expose] public section

set_option autoImplicit false

/-!
# The canonicalised, aliased export loop node against the model loop

`ComL.toLfundefPhysAbi` rewrites the export's loop node by `aliasRegBody acc out`
and `canonicalizeMemrefThread`. The second pass sends the result name of a
`STOREIDX` to its base, so on the name-keyed flag machine the store writes the
array at `out` in place and the feedback move is the self-copy `MOV out, out`.
This module runs that node on `lsemFuelMemF` and states its result against the
source fold `JLoopBodyN.denote`, the array the model loop
`loopBodyArrFullMN update` leaves at its accumulator.

## Contents

* **§1** `pullM τ s`: the state that holds at `r` what `s` holds at `τ r`;
  `StoreAgreesM.congr_args`: an agreement at depth `nArgs` reads argument cells
  only.
* **§2** `ThreadCert`: a certificate over the model chain `straightOpsMem` for a
  renaming `τ` that sends every store result of the accumulator thread to `out`
  (`ThreadRen`). `lsemStraightMem_thread` matches a run of the chain by a run of
  the renamed chain, through `JasminLsemExportRegAlloc.lsemStepMem_live`, with
  register names related unless their image is an already written body temporary
  and array names related unless their image is `out` and they are not the
  thread head.
* **§3–§4** `canonTail_run`, `canonBody_trip`: one pass of the canonicalised body
  from a state whose pullback agrees with the trip-`t` valuation lands in a state
  whose pullback agrees with the trip-`(t+1)` valuation at `JLoopBodyN.stepC`.
* **§5** `canonNodeRM_faithful`: the node (seed moves, zero-trip guard, flag
  back-edge) halts with the array at `out` decoding to
  `JLoopBodyN.denote ⟨m, update⟩ invs arr0`, through `flagNest_closed`.
* **§6** `forLoopLcmdNRtRM_map_eq_canonNodeRM`: the typed export node renamed by
  `ρ` is `canonNodeRM` at `τ = ρ ∘ σ`; `forLoopLcmdNRtRM_canon_wire`: its wire is
  the instruction stream of `canonicalizeMemrefThread (aliasRegBody acc out _)`
  when the alias map resolves as `κ`.

## Scope

The certificate requires every array read whose image is `out` to go through the
current thread head: no load or store goes through the accumulator argument or
an earlier store result once a later store has replaced it as the head. The
certificate is a hypothesis of the theorems; no instance is proved here.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc

/-! ## 1. The pullback of a state along a renaming -/

/-- The state that holds at a name `r` the register cell and the array cell the
    state `s` holds at `τ r`, with the program counter, the word memory and the carry
    and overflow flags of `s`. -/
def pullM (τ : String → String) (s : LstateM) : LstateM :=
  { reg := { lvm := fun r => s.reg.lvm (τ r), lpc := s.reg.lpc }
    larr := fun r => s.larr (τ r)
    lmem := s.lmem
    cf := s.cf
    of := s.of }

@[simp] theorem pullM_getW (τ : String → String) (s : LstateM) (r : String) (w : Nat) :
    (pullM τ s).reg.getW r w = s.reg.getW (τ r) w := rfl

@[simp] theorem pullM_getArr (τ : String → String) (s : LstateM) (r : String) (w n : Nat) :
    (pullM τ s).getArr r w n = s.getArr (τ r) w n := rfl

/-- At depth `nArgs` every in-scope variable resolves to an argument name. -/
theorem resolveVar_argName {nArgs : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (hlen : Γ.length = nArgs) (v : Ctxt.Var Γ t) :
    ∃ j, j < nArgs ∧
      operandName (resolveVar nArgs nArgs argName (fun _ => none) v) = argName j := by
  have hv : varIndex v < nArgs := hlen ▸ JasminLsemSimulation.varIndex_lt v
  refine ⟨nArgs - 1 - varIndex v, by omega, ?_⟩
  simp only [resolveVar, operandName]
  rw [ite_eq_left (by omega)]

/-- **Agreement reads argument cells only.** At depth `nArgs`, a state that reads
    every argument name's register and array as an agreeing state does agrees
    too. -/
theorem StoreAgreesM.congr_args {nArgs : Nat} {Γ : Ctxt jasminDialect}
    {s1 s2 : LstateM} {V : Ctxt.Valuation Γ} (hlen : Γ.length = nArgs)
    (h : StoreAgreesM nArgs nArgs s1 V)
    (hr : ∀ j, j < nArgs → ∀ w, s2.reg.getW (argName j) w = s1.reg.getW (argName j) w)
    (ha : ∀ j, j < nArgs → ∀ w n, s2.getArr (argName j) w n = s1.getArr (argName j) w n) :
    StoreAgreesM nArgs nArgs s2 V := by
  refine ⟨?_, ?_⟩
  · intro w' v
    obtain ⟨j, hj, hn⟩ := resolveVar_argName hlen v
    have := h.reg v
    rw [evalOperandN_resolveVar, hn] at this ⊢
    rw [hr j hj]
    exact this
  · intro w' n' v
    obtain ⟨j, hj, hn⟩ := resolveVar_argName hlen v
    have := h.arr v
    rw [hn] at this ⊢
    rw [ha j hj]
    exact this

/-! ## 2. The thread renaming on a straight chain -/

/-- The hypotheses on a renaming `τ` of the model chain's names at loop depth `d`:
    `S` marks the chain slots that hold a store. The empty name is fixed, the
    chain register of a slot outside `S` goes to the body temporary of that slot,
    the chain register of a slot in `S` goes to `out`, and neither `out` nor the
    image of an argument name is a body temporary. -/
structure ThreadRen (τ : String → String) (d nArgs : Nat) (S : Nat → Prop) (out : String) :
    Prop where
  /-- The empty name is fixed. -/
  fix : τ "" = ""
  /-- A slot outside `S` goes to its body temporary. -/
  tmp : ∀ k, nArgs ≤ k → ¬ S k → τ (regName k) = loopReg d k
  /-- A slot in `S` goes to `out`. -/
  thr : ∀ k, nArgs ≤ k → S k → τ (regName k) = out
  /-- The image of an argument name is no body temporary. -/
  arg : ∀ j k, j < nArgs → τ (argName j) ≠ loopReg d k
  /-- `out` is no body temporary. -/
  outL : ∀ k, out ≠ loopReg d k

/-- The register names related at chain depth `cd`: a name whose image is the body
    temporary of an earlier slot outside `S` is that slot's chain register. -/
def ThreadNr (τ : String → String) (d nArgs : Nat) (S : Nat → Prop) (cd : Nat)
    (r : String) : Prop :=
  ∀ k, nArgs ≤ k → k < cd → ¬ S k → τ r = loopReg d k → r = regName k

/-- The array names related while the thread head is `h`: a name whose image is
    `out` is `h`. -/
def ThreadNa (τ : String → String) (out h : String) (r : String) : Prop :=
  τ r = out → r = h

/-- A name the chain can read at depth `cd`: the empty name, an argument name, or
    the chain register of an earlier slot. -/
def Resolved (nArgs cd : Nat) (n : String) : Prop :=
  n = "" ∨ (∃ j, j < nArgs ∧ n = argName j) ∨ (∃ k, nArgs ≤ k ∧ k < cd ∧ n = regName k)

/-- `loopReg d` is injective in the slot. -/
theorem loopReg_injective (d : Nat) : Function.Injective (loopReg d) := by
  intro a b hab
  unfold loopReg at hab
  apply FreshNameInjective.natToString_injective
  have hd := congrArg String.toList hab
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

variable {τ : String → String} {d nArgs : Nat} {S : Nat → Prop} {out : String}

theorem ThreadNr.of_resolved (hτ : ThreadRen τ d nArgs S out) {cd : Nat} {n : String}
    (h : Resolved nArgs cd n) : ThreadNr τ d nArgs S cd n := by
  intro k hk _ hS he
  rcases h with rfl | ⟨j, hj, rfl⟩ | ⟨k', hk', _, rfl⟩
  · rw [hτ.fix] at he
    exact absurd he.symm (ne_empty_of_head? (head?_loopReg d k))
  · exact absurd he (hτ.arg j k hj)
  · by_cases hS' : S k'
    · rw [hτ.thr k' hk' hS'] at he
      exact absurd he (hτ.outL k)
    · rw [hτ.tmp k' hk' hS'] at he
      rw [loopReg_injective d he]

/-- **The thread certificate of a chain** from depth `cd` and thread head `h` to
    the final head `hE`. Every instruction reads resolved names, reads no array
    whose image is `out` other than the head, and is either a register binding of
    a slot outside `S` that writes `regName cd`, or a store of a slot in `S`
    whose result `regName cd` becomes the head. -/
def ThreadCert (τ : String → String) (nArgs : Nat) (S : Nat → Prop) (out : String) :
    List LinstrRM → Nat → String → String → Prop
  | [], _, h, hE => h = hE
  | i :: is, cd, h, hE =>
      (∀ n ∈ useNames i.1, Resolved nArgs cd n)
      ∧ (∀ b, arrUse? i = some b → τ b = out → b = h)
      ∧ ((storeHit? i = none ∧ defNames i.1 = [regName cd] ∧ ¬ S cd
            ∧ ThreadCert τ nArgs S out is (cd + 1) h hE)
          ∨ (storeHit? i = some (regName cd) ∧ S cd
            ∧ ThreadCert τ nArgs S out is (cd + 1) (regName cd) hE))

/-- **The chain under the thread renaming.** For a chain with a thread
    certificate, a run of the chain from a state related on the names of depth
    `cd` and head `h` is matched by a run of the renamed chain, into a state
    related on the names of the final depth and the final head, whose image is
    `out`. -/
theorem lsemStraightMem_thread (hτ : ThreadRen τ d nArgs S out) :
    ∀ (chain : List LinstrRM) (cd : Nat) (h hE : String), nArgs ≤ cd → τ h = out →
      ThreadCert τ nArgs S out chain cd h hE →
      ∀ {s s' t : LstateM},
        RelM2 τ (ThreadNr τ d nArgs S cd) (ThreadNa τ out h) s s' →
        lsemStraightMem chain s = some t →
        ∃ t', lsemStraightMem (chain.map (renRM τ)) s' = some t'
          ∧ RelM2 τ (ThreadNr τ d nArgs S (cd + chain.length)) (ThreadNa τ out hE) t t'
          ∧ τ hE = out := by
  intro chain
  induction chain with
  | nil =>
      intro cd h hE _ hh hc s s' t hR hrun
      obtain rfl : h = hE := hc
      cases hrun
      exact ⟨s', rfl, hR, hh⟩
  | cons i is ih =>
      intro cd h hE hcd hh hc s s' t hR hrun
      obtain ⟨hu, hau, hshape⟩ := hc
      rw [lsemStraightMem_cons] at hrun
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s1 =>
      rw [hstep] at hrun
      have hemp : ThreadNr τ d nArgs S cd "" := ThreadNr.of_resolved hτ (Or.inl rfl)
      have huN : ∀ n ∈ useNames i.1, ThreadNr τ d nArgs S cd n :=
        fun n hn => ThreadNr.of_resolved hτ (hu n hn)
      rcases hshape with ⟨hst, hdef, hS, hrest⟩ | ⟨hst, hS, hrest⟩
      · have hKr : Keeps τ (ThreadNr τ d nArgs S cd) (ThreadNr τ d nArgs S (cd + 1))
            (memRegDefs i) := by
          rw [show memRegDefs i = [regName cd] from by simp [memRegDefs, hst, hdef]]
          intro r hr
          by_cases hrd : r = regName cd
          · exact Or.inl (by rw [hrd])
          · refine Or.inr ⟨fun k hk hkc => hr k hk (by omega), ?_⟩
            intro x hx
            obtain rfl : x = regName cd := by simpa using hx
            rw [hτ.tmp cd hcd hS]
            exact fun he => hrd (hr cd hcd (by omega) hS he)
        have hKa : Keeps τ (ThreadNa τ out h) (ThreadNa τ out h) (memArrDefs i) := by
          rw [show memArrDefs i = [] from by simp [memArrDefs, hst]]
          exact fun r hr => Or.inr ⟨hr, by simp⟩
        obtain ⟨s1', hs1', hR1⟩ := lsemStepMem_live hemp hτ.fix i huN
          (fun b hb => hau b hb) hKr hKa hR hstep
        obtain ⟨t', ht', hRt, hE'⟩ := ih (cd + 1) h hE (by omega) hh hrest hR1 hrun
        refine ⟨t', ?_, ?_, hE'⟩
        · rw [List.map_cons, lsemStraightMem_cons, hs1']
          exact ht'
        · rw [List.length_cons, show cd + (is.length + 1) = cd + 1 + is.length from by omega]
          exact hRt
      · have hKr : Keeps τ (ThreadNr τ d nArgs S cd) (ThreadNr τ d nArgs S (cd + 1))
            (memRegDefs i) := by
          rw [show memRegDefs i = [] from by simp [memRegDefs, hst]]
          intro r hr
          refine Or.inr ⟨fun k hk hkc => hr k hk (by omega), by simp⟩
        have hKa : Keeps τ (ThreadNa τ out h) (ThreadNa τ out (regName cd)) (memArrDefs i) := by
          rw [show memArrDefs i = [regName cd] from by simp [memArrDefs, hst]]
          intro r hr
          by_cases hrd : r = regName cd
          · exact Or.inl (by rw [hrd])
          · refine Or.inr ⟨fun he => absurd (hr he) hrd, ?_⟩
            intro x hx
            obtain rfl : x = regName cd := by simpa using hx
            rw [hτ.thr cd hcd hS]
            exact fun he => hrd (hr he)
        obtain ⟨s1', hs1', hR1⟩ := lsemStepMem_live hemp hτ.fix i huN
          (fun b hb => hau b hb) hKr hKa hR hstep
        obtain ⟨t', ht', hRt, hE'⟩ := ih (cd + 1) (regName cd) hE (by omega)
          (hτ.thr cd hcd hS) hrest hR1 hrun
        refine ⟨t', ?_, ?_, hE'⟩
        · rw [List.map_cons, lsemStraightMem_cons, hs1']
          exact ht'
        · rw [List.length_cons, show cd + (is.length + 1) = cd + 1 + is.length from by omega]
          exact hRt

/-! ## 3. The tail of the canonicalised body -/

/-- The feedback move of the canonicalised body: absent, or the self-copy
    `MOV out, out`. -/
def canonFeedback (out : String) (absent : Bool) : List LinstrRM :=
  if absent then []
  else [(.Lopn [.reg out] (withWidthTag 64 "MOV") [.reg out], MemTag.reg none)]

/-- Writing a register with its own cell changes no read. -/
theorem getW_setReg_self (s : LstateM) (r x : String) (w : Nat) :
    (s.setReg r (s.reg.lvm r).2).reg.getW x w = s.reg.getW x w := by
  by_cases h : x = r
  · subst h
    have hc : (s.setReg x (s.reg.lvm x).2).reg.lvm x = s.reg.lvm x := by
      simp [LstateM.setReg, LstateN.setReg]
    unfold LstateN.getW
    rw [hc]
  · rw [LstateM.reg_setReg]
    exact LstateN.getW_setReg_other _ _ _ _ _ h

/-- The extended step of an instruction that is neither the flag compare nor a
    register copy is the flag machine's straight-line step `stepMemF`. -/
theorem fstepF_of_plain (i : LinstrRM) (hc : cmpArgs? i = none) (hm : movRegArgs? i = none)
    (s : LstateM) (zf : Bool) : fstepF i s zf = (stepMemF i s).map (fun b => (b, zf)) := by
  unfold fstepF
  rw [hc, hm]

/-- The extended step of the self-copy `MOV out, out`. -/
theorem fstepF_movSelf (out : String) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg out] (withWidthTag 64 "MOV") [.reg out], MemTag.reg none) s zf
      = some ((s.setReg out (s.reg.lvm out).2).nextPc, zf) := by
  unfold fstepF
  simp only [cmpArgs?, movRegArgs?]
  rw [ite_eq_left (show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide)]
  rfl

/-- **The tail of the canonicalised body.** From a state whose index and counter
    read at width `64` and whose touched registers read at width `64`, the
    feedback move, the index and counter updates and the invariant touches run:
    the array carrier is unchanged, every register other than the index and the
    counter reads as before, the index cell holds the incremented index and the
    counter reads the decremented count. -/
theorem canonTail_run (d : Nat) (out : String) (absent : Bool) (regs : List String)
    (u : LstateM) (zf : Bool) (vi vn : BitVec 64)
    (hidx : u.reg.getW (loopIdx d) 64 = some vi)
    (hctr : u.reg.getW (loopCtr d) 64 = some vn)
    (hregs : ∀ r ∈ regs, (u.reg.getW r 64).isSome)
    (hic : loopIdx d ≠ loopCtr d) :
    ∃ u' zf', runStraightF (canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d regs)
        u zf = some (u', zf')
      ∧ u'.larr = u.larr
      ∧ (∀ x w, x ≠ loopIdx d → x ≠ loopCtr d → u'.reg.getW x w = u.reg.getW x w)
      ∧ u'.reg.lvm (loopIdx d) = ⟨64, vi + 1#64⟩
      ∧ u'.reg.getW (loopCtr d) 64 = some (vn - 1#64) := by
  -- the feedback move
  obtain ⟨u1, hu1, hl1, hr1⟩ : ∃ u1, runStraightF (canonFeedback out absent) u zf = some (u1, zf)
      ∧ u1.larr = u.larr ∧ ∀ x w, u1.reg.getW x w = u.reg.getW x w := by
    unfold canonFeedback
    cases absent with
    | true => exact ⟨u, rfl, rfl, fun _ _ => rfl⟩
    | false =>
        refine ⟨(u.setReg out (u.reg.lvm out).2).nextPc, ?_, rfl, fun x w => ?_⟩
        · simp only [Bool.false_eq_true, ite_false, runStraightF_cons, fstepF_movSelf,
            Option.bind_some, runStraightF_nil]
        · rw [LstateM.reg_nextPc, LstateN.getW_nextPc]
          exact getW_setReg_self u out x w
  -- the index advance
  have hadd : withWidthTag 64 "ADD" = "ADD:64" := by decide
  have hsub : withWidthTag 64 "SUB" = "SUB:64" := by decide
  have h2 := lsemStepMem_add64Imm (loopIdx d) (loopIdx d) 1 vi u1 ((hr1 _ _).trans hidx)
  set u2 := withALUFlags
    (.Lopn [.reg (loopIdx d)] "ADD:64" [.reg (loopIdx d), .imm 1], MemTag.reg none)
    u1 (u1.setReg (loopIdx d) (vi + BitVec.ofNat 64 1)).nextPc with hu2
  have hctr2 : u2.reg.getW (loopCtr d) 64 = some vn := by
    rw [hu2, withALUFlags_reg]
    rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _ (Ne.symm hic), hr1]
    exact hctr
  have h3 := lsemStepMem_sub64Imm (loopCtr d) (loopCtr d) 1 vn u2 hctr2
  set u3 := withALUFlags
    (.Lopn [.reg (loopCtr d)] "SUB:64" [.reg (loopCtr d), .imm 1], MemTag.reg none)
    u2 (u2.setReg (loopCtr d) (vn - BitVec.ofNat 64 1)).nextPc with hu3
  have hread3 : ∀ x w, x ≠ loopIdx d → x ≠ loopCtr d → u3.reg.getW x w = u.reg.getW x w := by
    intro x w hx1 hx2
    rw [hu3, withALUFlags_reg]
    rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _ hx2, hu2, withALUFlags_reg]
    rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _ hx1, hr1]
  have hctr3 : u3.reg.getW (loopCtr d) 64 = some (vn - 1#64) := by
    rw [hu3, withALUFlags_reg]
    exact LstateM.getW_setReg_nextPc_same u2 (loopCtr d) _
  have hidx3 : u3.reg.getW (loopIdx d) 64 = some (vi + 1#64) := by
    rw [hu3, withALUFlags_reg]
    rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _ hic, hu2, withALUFlags_reg]
    exact LstateM.getW_setReg_nextPc_same u1 (loopIdx d) _
  have hregs3 : ∀ r ∈ regs, (u3.reg.getW r 64).isSome := by
    intro r hr
    by_cases h1 : r = loopIdx d
    · rw [h1, hidx3]; rfl
    · by_cases h2' : r = loopCtr d
      · rw [h2', hctr3]; rfl
      · rw [hread3 r 64 h1 h2']; exact hregs r hr
  obtain ⟨zf', htouch⟩ := runStraightF_cmpTouchRM (loopCtr d) regs u3 zf
    (by rw [hctr3]; rfl) hregs3
  refine ⟨u3.setLpc (u3.lpc + regs.length), zf', ?_, ?_, ?_, ?_, ?_⟩
  · have hadv : runStraightF (loopAdvanceRM d) u1 zf = some (u3, zf) := by
      unfold loopAdvanceRM
      rw [runStraightF_cons, hadd,
        fstepF_of_plain _ (by simp [cmpArgs?, withWidthTag]) (by simp [movRegArgs?]),
        stepMemF_of_lsemStepMem h2, Option.map_some, Option.bind_some, runStraightF_cons, hsub,
        fstepF_of_plain _ (by simp [cmpArgs?, withWidthTag]) (by simp [movRegArgs?]),
        stepMemF_of_lsemStepMem h3, Option.map_some, Option.bind_some, runStraightF_nil]
    rw [List.append_assoc, runStraightF_append, hu1, Option.bind_some, runStraightF_append,
      hadv, Option.bind_some]
    exact htouch
  · show u3.larr = u.larr
    simp only [hu3, hu2, withALUFlags_larr, LstateM.larr_nextPc, LstateM.larr_setReg]
    exact hl1
  · intro x w hx1 hx2
    rw [getW_setLpc]
    exact hread3 x w hx1 hx2
  · show u3.reg.lvm (loopIdx d) = _
    rw [hu3, hu2]
    simp [withALUFlags_reg, LstateM.nextPc, LstateM.setReg, hic]
  · rw [getW_setLpc]
    exact hctr3

/-! ## 4. One trip of the canonicalised body -/

/-- The hypotheses on the renaming `τ` from the model loop's names to the names of
    the canonicalised node at depth `d` with `nInv` invariants: the thread
    hypotheses at `nInv + 2` arguments, the accumulator argument goes to `out`,
    the index argument to `Lidx<d>`, the counter name is fixed, and `out`, the
    index, the counter and the images of the other arguments are distinct. -/
structure CanonRen (τ : String → String) (d nInv : Nat) (S : Nat → Prop) (out : String) :
    Prop extends ThreadRen τ d (nInv + 2) S out where
  /-- The accumulator argument goes to `out`. -/
  acc : τ (argName (nInv + 1)) = out
  /-- The index argument goes to the loop index. -/
  idx : τ (argName nInv) = loopIdx d
  /-- The counter name is fixed. -/
  ctr : τ (loopCtr d) = loopCtr d
  /-- No argument other than the accumulator goes to `out`. -/
  argOut : ∀ j, j ≤ nInv → τ (argName j) ≠ out
  /-- No invariant argument goes to the loop index. -/
  invIdx : ∀ j, j < nInv → τ (argName j) ≠ loopIdx d
  /-- No invariant argument goes to the counter. -/
  invCtr : ∀ j, j < nInv → τ (argName j) ≠ loopCtr d
  /-- `out` is not the loop index. -/
  outIdx : out ≠ loopIdx d
  /-- `out` is not the counter. -/
  outCtr : out ≠ loopCtr d
  /-- The loop index is not the counter. -/
  idxCtr : loopIdx d ≠ loopCtr d
  /-- The counter is no body temporary. -/
  ctrL : ∀ k, loopCtr d ≠ loopReg d k

/-- Renaming keeps a body plain. -/
theorem plainLopnBody_map_renRM (τ : String → String) {body : List LinstrRM}
    (h : PlainLopnBody body) : PlainLopnBody (body.map (renRM τ)) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨⟨dd, o, ss, hd⟩, hc, hm⟩ := h j hj
  refine ⟨⟨_, o, _, by show renLinstrR τ j.1 = _; rw [hd]; rfl⟩, ?_, ?_⟩
  · rw [cmpArgs?_ren, hc]; rfl
  · rw [movRegArgs?_ren, hm]; rfl

/-- Two states holding the same array cell read the same array. -/
theorem getArr_congr_cell {s1 s2 : LstateM} {r1 r2 : String} (h : s1.larr r1 = s2.larr r2)
    (w n : Nat) : s1.getArr r1 w n = s2.getArr r2 w n := by
  unfold LstateM.getArr
  rw [h]

/-- Two states holding the same register cell read the same register. -/
theorem getW_congr_cell {s1 s2 : LstateN} {r1 r2 : String} (h : s1.lvm r1 = s2.lvm r2)
    (w : Nat) : s1.getW r1 w = s2.getW r2 w := by
  unfold LstateN.getW
  rw [h]

/-- A successful shaped array read determines the cell. -/
theorem larr_of_getArr {s : LstateM} {r : String} {w n : Nat} {a : Fin n → BitVec w}
    (h : s.getArr r w n = some a) : s.larr r = ⟨w, n, a⟩ := by
  unfold LstateM.getArr at h
  generalize s.larr r = c at h
  obtain ⟨w0, n0, a0⟩ := c
  split at h
  · next hw =>
      split at h
      · next hn =>
          dsimp only at hw hn
          subst hw; subst hn
          cases h
          rfl
      · exact absurd h (by simp)
  · exact absurd h (by simp)

variable {invTys : Ctxt jasminDialect}

/-- **One trip of the canonicalised body.** Let `τ` satisfy `CanonRen` and let the
    model chain of an `ArrMemN` update carry a thread certificate from the
    accumulator argument to the chain's return array. From a state whose pullback
    along `τ` agrees with the trip-`t` valuation, whose invariant base registers
    read at width `64` and whose counter reads `vn`, the renamed chain followed by
    the feedback move, the index and counter updates and the touches runs to a
    state whose pullback agrees with the trip-`(t+1)` valuation at the stepped
    array `JLoopBodyN.stepC`, with the invariant base registers readable and the
    counter decremented. -/
theorem canonBody_trip {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (t : Nat) (arrt : Fin n → BitVec w) (s' : LstateM)
    (hag : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s')
      (tripValArrMN invs t arrt))
    (hinv : ∀ j, j < invTys.length → (s'.reg.getW (τ (argName j)) 64).isSome)
    (vn : BitVec 64) (hn : s'.reg.getW (loopCtr d) 64 = some vn) (zf : Bool) :
    ∃ s'' zf',
      runStraightF
          ((straightOpsMem (invTys.length + 2) update (invTys.length + 2)).map (renRM τ)
            ++ (canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d regs)) s' zf
        = some (s'', zf')
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s'')
          (tripValArrMN invs (t + 1) (JLoopBodyN.stepC update invs t arrt))
      ∧ (∀ j, j < invTys.length → (s''.reg.getW (τ (argName j)) 64).isSome)
      ∧ s''.reg.getW (loopCtr d) 64 = some (vn - 1#64) := by
  obtain ⟨stc, hrunC, hFrC, hretC⟩ :=
    ArrMemN.straightOps_full hupd (nArgs := invTys.length + 2)
      (curDepth := invTys.length + 2) rfl le_rfl hag
  set stepv : Fin n → BitVec w := JLoopBodyN.stepC update invs t arrt with hstepv
  have hR0 : RelM2 τ (ThreadNr τ d (invTys.length + 2) S (invTys.length + 2))
      (ThreadNa τ out (accRegMN invTys)) (pullM τ s') s' :=
    ⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩
  obtain ⟨t', hrun', hRt, hE⟩ := lsemStraightMem_thread hτ.toThreadRen _ _ _ _ le_rfl
    hτ.acc hcert hR0 hrunC
  have hargN : ∀ j, j < invTys.length + 2 → ∀ cd, ThreadNr τ d (invTys.length + 2) S cd
      (argName j) := fun j hj cd => ThreadNr.of_resolved hτ.toThreadRen
        (Or.inr (Or.inl ⟨j, hj, rfl⟩))
  have hreg : ∀ j, j < invTys.length + 2 → ∀ w',
      t'.reg.getW (τ (argName j)) w' = s'.reg.getW (τ (argName j)) w' := by
    intro j hj w'
    rw [hRt.1.getW (hargN j hj _) w',
      hFrC.1 (argName j) w' (fun k _ => (JasminLsemSimulation.regName_ne_argName k j).symm)]
    rfl
  have harr : ∀ j, j ≤ invTys.length → ∀ w' n',
      t'.getArr (τ (argName j)) w' n' = s'.getArr (τ (argName j)) w' n' := by
    intro j hj w' n'
    rw [hRt.getArr (fun he => absurd he (hτ.argOut j hj)) w' n',
      hFrC.2 (argName j) w' n' (fun k _ => (JasminLsemSimulation.regName_ne_argName k j).symm)]
    rfl
  have hout : t'.larr out = ⟨w, n, stepv⟩ := by
    have h1 := hRt.2.1 (loopBodyRetArrMN update) (fun _ => rfl)
    rw [hE] at h1
    rw [h1]
    exact larr_of_getArr hretC
  have hctr : t'.reg.getW (loopCtr d) 64 = some vn := by
    have h1 := hRt.1.getW (r := loopCtr d)
      (fun k _ _ _ he => absurd (hτ.ctr ▸ he) (hτ.ctrL k)) 64
    rw [hτ.ctr] at h1
    rw [h1, hFrC.1 (loopCtr d) 64 (fun k _ => loopCtr_ne_regName d k)]
    show s'.reg.getW (τ (loopCtr d)) 64 = some vn
    rw [hτ.ctr]
    exact hn
  have hidx : t'.reg.getW (loopIdx d) 64 = some (BitVec.ofNat 64 t) := by
    have h1 := hreg invTys.length (by omega) 64
    rw [hτ.idx] at h1
    rw [h1]
    have h2 := tripAgree_getW_idx hag
    rw [← hτ.idx]
    exact h2
  have hregs' : ∀ r ∈ regs, (t'.reg.getW r 64).isSome := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := hregs r hr
    rw [hreg j (by omega) 64]
    exact hinv j hj
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _
    (plainLopnBody_map_renRM τ (arrMemN_straightOpsMem_plain hupd _ _)) s' t' zf hrun'
  obtain ⟨u', zf', hrunT, hl0, hread0, hcell, hctr'⟩ := canonTail_run d out absent regs
    { t' with cf := c, of := o } zf (BitVec.ofNat 64 t) vn hidx hctr hregs' hτ.idxCtr
  have hl : u'.larr = t'.larr := hl0
  have hread : ∀ x w, x ≠ loopIdx d → x ≠ loopCtr d → u'.reg.getW x w = t'.reg.getW x w :=
    hread0
  have hnotIC : ∀ j, j < invTys.length + 2 → j ≠ invTys.length →
      τ (argName j) ≠ loopIdx d ∧ τ (argName j) ≠ loopCtr d := by
    intro j hj hjn
    by_cases hja : j = invTys.length + 1
    · subst hja
      rw [hτ.acc]
      exact ⟨hτ.outIdx, hτ.outCtr⟩
    · exact ⟨hτ.invIdx j (by omega), hτ.invCtr j (by omega)⟩
  refine ⟨u', zf', ?_, ?_, ?_, hctr'⟩
  · rw [runStraightF_append, hF, Option.bind_some]
    exact hrunT
  · have hm3 := tripAgree_setReg_idx (tripAgree_setArr_acc hag stepv)
      (BitVec.ofNat 64 (t + 1))
    refine StoreAgreesM.congr_args rfl hm3 ?_ ?_
    · intro j hj w'
      rw [pullM_getW]
      by_cases hjn : j = invTys.length
      · subst hjn
        rw [hτ.idx]
        refine getW_congr_cell ?_ w'
        rw [hcell]
        show _ = (if idxRegMN invTys = idxRegMN invTys then _ else _)
        rw [ite_eq_left rfl, BitVec.ofNat_add]
      · obtain ⟨h1, h2⟩ := hnotIC j hj hjn
        rw [hread _ w' h1 h2, hreg j hj w', LstateM.reg_setReg,
          LstateN.getW_setReg_other _ _ _ _ _
            (show argName j ≠ idxRegMN invTys from JasminLsemSimulation.argName_ne hjn)]
        rfl
    · intro j hj w' n'
      rw [pullM_getArr, LstateM.getArr_setReg]
      by_cases hja : j = invTys.length + 1
      · subst hja
        rw [hτ.acc]
        refine getArr_congr_cell ?_ w' n'
        rw [hl, hout]
        show _ = (if accRegMN invTys = accRegMN invTys then _ else _)
        rw [ite_eq_left rfl]
      · rw [LstateM.getArr_congr_larr hl, harr j (by omega) w' n',
          LstateM.getArr_setArr_other _ _ _ _ _ _
            (show argName j ≠ accRegMN invTys from JasminLsemSimulation.argName_ne hja)]
        rfl
  · intro j hj
    obtain ⟨h1, h2⟩ := hnotIC j (by omega) (by omega)
    rw [hread _ 64 h1 h2, hreg j (by omega) 64]
    exact hinv j hj

/-! ## 5. The canonicalised node and its run -/

/-- The looped segment of the canonicalised node: the model chain renamed by `τ`,
    the feedback move, the index and counter updates, the invariant touches. -/
def canonBodyRM (τ : String → String) (d : Nat) (out : String) {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (absent : Bool) (regs : List String) : List LinstrRM :=
  (straightOpsMem (invTys.length + 2) update (invTys.length + 2)).map (renRM τ)
    ++ (canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d regs)

/-- The seed moves of the canonicalised node: the self-copy of `out`, the index
    seed, and the counter seed from the register `c`. -/
def canonSeedsRM (d : Nat) (out c : String) : List LinstrRM :=
  [ (.Lopn [.reg out] (withWidthTag 64 "MOV") [.reg out], MemTag.reg none)
  , (.Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0], MemTag.reg none)
  , (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [.reg c], MemTag.reg none) ]

/-- **The canonicalised node**: the seed moves, then the zero-trip guarded flag
    loop over the canonicalised body. -/
def canonNodeRM (τ : String → String) (d : Nat) (out c : String) {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (absent : Bool) (regs : List String) : List LinstrRM :=
  canonSeedsRM d out c
    ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
        (canonBodyRM τ d out update absent regs)

/-- Every instruction of the canonicalised body is an `Lopn`. -/
theorem canonBodyRM_isLopn (τ : String → String) (d : Nat) (out : String) {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (absent : Bool) (regs : List String) :
    ∀ i ∈ canonBodyRM τ d out update absent regs, IsLopn i := by
  intro i hi
  simp only [canonBodyRM, List.mem_append, List.mem_map] at hi
  rcases hi with ⟨j, hj, rfl⟩ | (hi | hi) | hi
  · obtain ⟨dd, o, ss, hd⟩ := straightOpsMem_isLopn update _ _ j hj
    exact ⟨_, o, _, by show renLinstrR τ j.1 = _; rw [hd]; rfl⟩
  · unfold canonFeedback at hi
    split at hi
    · simp at hi
    · simp only [List.mem_singleton] at hi; subst hi; exact ⟨_, _, _, rfl⟩
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

/-- The pullback commutes with the program-counter write. -/
theorem pullM_setLpc (τ : String → String) (s : LstateM) (pc : Nat) :
    pullM τ (s.setLpc pc) = (pullM τ s).setLpc pc := rfl

/-- **The run of the canonicalised body with its counter.** From a seed whose
    pullback agrees with the trip-`0` valuation, with readable invariant base
    registers and a counter reading `v0`, every trip count `t` has a trip state
    whose pullback agrees with the source fold at `t` and whose counter reads
    `v0 - t`. -/
theorem canonBodyRM_run {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (q : Nat) (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s0)
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < invTys.length → (s0.reg.getW (τ (argName j)) 64).isSome)
    (v0 : BitVec 64) (hv0 : s0.reg.getW (loopCtr d) 64 = some v0) :
    ∀ t, ∃ bt,
      runBoundedStraightF (canonBodyRM τ d out update absent regs) q t s0 = some bt
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ bt)
          (tripValArrMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs arr0))
      ∧ (∀ j, j < invTys.length → (bt.reg.getW (τ (argName j)) 64).isSome)
      ∧ bt.reg.getW (loopCtr d) 64 = some (v0 - BitVec.ofNat 64 t) := by
  intro t
  induction t with
  | zero =>
      refine ⟨s0, rfl, hseed, hinv, ?_⟩
      rw [hv0]
      simp
  | succ k ih =>
      obtain ⟨bk, hbk, hAgk, hinvk, hnk⟩ := ih
      obtain ⟨bt', zb, hbt', hAg', hinv', hn'⟩ := canonBody_trip update hupd hτ hcert
        absent regs hregs invs k (JLoopBodyN.denote ⟨k, update⟩ invs arr0) bk hAgk hinvk
        _ hnk false
      refine ⟨bt'.setLpc q, ?_, ?_, ?_, ?_⟩
      · rw [runBoundedStraightF_succ_right, hbk, Option.bind_some]
        show (runStraightF (canonBodyRM τ d out update absent regs) bk false).map _ = _
        rw [canonBodyRM, hbt', Option.map_some]
      · rw [JLoopBodyN.denote_succ, pullM_setLpc]
        exact StoreAgreesM.setLpc hAg' q
      · intro j hj
        rw [getW_setLpc]
        exact hinv' j hj
      · rw [getW_setLpc, hn']
        congr 1
        rw [BitVec.sub_sub, BitVec.ofNat_add]

/-- The extended step of a register copy `MOV dst, src`. -/
theorem fstepF_movReg (dst src : String) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], MemTag.reg none) s zf
      = some ((s.setReg dst (s.reg.lvm src).2).nextPc, zf) := by
  unfold fstepF
  simp only [cmpArgs?, movRegArgs?]
  rw [ite_eq_left (show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide)]
  rfl

/-- The memory step of the immediate move `MOV dst, #k` at width `64`. -/
theorem lsemStepMem_movImm64 (dst : String) (k : Nat) (st : LstateM) :
    lsemStepMem (LinstrR.Lopn [.reg dst] (withWidthTag 64 "MOV") [.imm k], MemTag.reg none) st
      = some ((st.setReg dst (BitVec.ofNat 64 k)).nextPc) := by
  have hmov : withWidthTag 64 "MOV" = "MOV:64" := by decide
  have hstrip : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
  have hwidth : widthFromTag "MOV:64" = 64 := by decide +kernel
  rw [hmov]
  have hstep : JasminLsemCast.lsemStepCast
      (LinstrR.Lopn [.reg dst] "MOV:64" [.imm k], none) st.reg
      = some ((st.reg.setReg dst (BitVec.ofNat 64 k)).nextPc) := by
    rw [JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
      JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
      JasminLsemShift.lsemStepSh_of_not_sar _ _ (by simp [JasminLsemShift.sarStruct?])]
    simp only [lsemStepN, hstrip, ite_true]
    rw [hwidth]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-- **The seed moves.** They run from any state; the array carrier is unchanged,
    every register other than the counter reads as in the entry state with the
    index zeroed, and the counter reads what `c` read at entry. -/
theorem canonSeedsRM_run (d : Nat) (out c : String) (hc : c ≠ loopIdx d) (b0 : LstateM)
    (zf : Bool) :
    ∃ b3, runStraightF (canonSeedsRM d out c) b0 zf = some (b3, zf)
      ∧ b3.larr = b0.larr
      ∧ (∀ x w, x ≠ loopCtr d →
          b3.reg.getW x w = (b0.setReg (loopIdx d) (0#64)).reg.getW x w)
      ∧ (∀ w, b3.reg.getW (loopCtr d) w = b0.reg.getW c w) := by
  set b1 := (b0.setReg out (b0.reg.lvm out).2).nextPc with hb1
  set b2 := (b1.setReg (loopIdx d) (BitVec.ofNat 64 0)).nextPc with hb2
  set b3 := (b2.setReg (loopCtr d) (b2.reg.lvm c).2).nextPc with hb3
  have hr1 : ∀ x w, b1.reg.getW x w = b0.reg.getW x w := by
    intro x w
    rw [hb1, LstateM.reg_nextPc, LstateN.getW_nextPc]
    exact getW_setReg_self b0 out x w
  refine ⟨b3, ?_, rfl, ?_, ?_⟩
  · unfold canonSeedsRM
    rw [runStraightF_cons, fstepF_movReg, Option.bind_some, runStraightF_cons,
      fstepF_of_plain _ (by simp [cmpArgs?]) (by simp [movRegArgs?]),
      stepMemF_of_quiet rfl rfl rfl, lsemStepMem_movImm64, Option.map_some, Option.bind_some,
      runStraightF_cons,
      fstepF_movReg, Option.bind_some, runStraightF_nil]
  · intro x w hx
    rw [hb3, LstateM.getW_setReg_nextPc_other _ _ _ _ _ hx]
    by_cases hxi : x = loopIdx d
    · subst hxi
      refine getW_congr_cell ?_ w
      simp [hb2, LstateM.nextPc, LstateM.setReg]
    · rw [hb2, LstateM.getW_setReg_nextPc_other _ _ _ _ _ hxi, hr1, LstateM.reg_setReg,
        LstateN.getW_setReg_other _ _ _ _ _ hxi]
  · intro w
    have h1 : b3.reg.getW (loopCtr d) w = b2.reg.getW c w := by
      refine getW_congr_cell ?_ w
      simp [hb3, LstateM.nextPc, LstateM.setReg]
    rw [h1, hb2, LstateM.getW_setReg_nextPc_other _ _ _ _ _ hc, hr1]

/-- Label positions behind the three seed moves. -/
theorem findLabelMem_canonSeedsRM (l : LLabel) (d : Nat) (out c : String)
    (rest : List LinstrRM) :
    findLabelMem l (canonSeedsRM d out c ++ rest) = (findLabelMem l rest).map (· + 3) := by
  unfold findLabelMem JasminLsemLabeled.findLabel canonSeedsRM
  simp only [List.cons_append, List.nil_append, List.map_cons, List.findIdx?_cons]
  have hl : ∀ (ds : List LOperand) (o : String) (ss : List LOperand),
      JasminLsemLabeled.isLabel l (.Lopn ds o ss) = false := fun _ _ _ => rfl
  cases List.findIdx? (JasminLsemLabeled.isLabel l) (rest.map Prod.fst) <;> simp [hl]

/-- **The canonicalised node computes the model loop.** Let `τ` satisfy `CanonRen`
    and let the model chain of an `ArrMemN` update carry a thread certificate from
    the accumulator argument to the chain's return array. Run the canonicalised
    node on the flag machine from program counter `0`, from a state whose
    pullback along `τ`, with the index zeroed, agrees with the trip-`0` valuation
    at the seed array `arr0`, whose invariant base registers read at width `64`,
    and whose count register `c` reads `m < 2^64`. The run halts, and the array
    at `out` decodes to the source fold `JLoopBodyN.denote ⟨m, update⟩ invs arr0`,
    the array the model loop leaves at its accumulator. -/
theorem canonNodeRM_faithful {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (hτ : CanonRen τ d invTys.length S out)
    (hcert : ThreadCert τ (invTys.length + 2) S out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update))
    (absent : Bool) (regs : List String)
    (hregs : ∀ r ∈ regs, ∃ j, j < invTys.length ∧ r = τ (argName j))
    (invs : Ctxt.Valuation invTys) (fn : String) (c : String) (hc : c ≠ loopIdx d)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM τ (b0.setReg (loopIdx d) (0#64))) (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < invTys.length → (b0.reg.getW (τ (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64) (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn (canonNodeRM τ d out c update absent regs)) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base out w n
            = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0) := by
  have hBlopn := canonBodyRM_isLopn τ d out update absent regs
  set B := canonBodyRM τ d out update absent regs with hB
  set blks : List FBlock :=
    [.straight (canonSeedsRM d out c),
     .guarded d (d + 0x40000000) (loopCtr d) [.straight B]] with hblks
  have hflat : flatFL blks = canonNodeRM τ d out c update absent regs := by
    simp [hblks, canonNodeRM, hB]
  have hok : FBlocksOK blks := by
    simp only [hblks, FBlocksOK_cons, FBlocksOK_nil, FBlockOK_guarded, FBlockOK_straight,
      and_true]
    refine ⟨?_, hBlopn⟩
    intro i hi
    simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  have hres : FBlocksResolve (singletonProgM fn (flatFL blks)) blks 0 := by
    rw [hflat]
    simp only [hblks, FBlocksResolve_cons, FBlocksResolve_nil, FBlockResolves_guarded,
      FBlockResolves_straight, and_true, true_and, fflat_straight, fflatFL_cons, fflatFL_nil,
      List.append_nil]
    show findLabelMem d (canonNodeRM τ d out c update absent regs) = _
      ∧ findLabelMem (d + 0x40000000) (canonNodeRM τ d out c update absent regs) = _
    unfold canonNodeRM
    rw [findLabelMem_canonSeedsRM, findLabelMem_canonSeedsRM, findLabelMem_guarded_top,
      findLabelMem_guarded_endL _ _ _ _ hBlopn
        (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))]
    refine ⟨?_, ?_⟩ <;> simp [canonSeedsRM]
    omega
  -- the seed moves
  obtain ⟨b3, hseeds, hl3, hr3, hc3⟩ := canonSeedsRM_run d out c hc b0 zf
  have hargCtr : ∀ j, j < invTys.length + 2 → τ (argName j) ≠ loopCtr d := by
    intro j hj
    by_cases h1 : j = invTys.length + 1
    · subst h1; rw [hτ.acc]; exact hτ.outCtr
    · by_cases h2 : j = invTys.length
      · subst h2; rw [hτ.idx]; exact hτ.idxCtr
      · exact hτ.invCtr j (by omega)
  have hAg3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ b3)
      (tripValArrMN invs 0 arr0) := by
    refine StoreAgreesM.congr_args rfl hseed ?_ ?_
    · intro j hj w'
      rw [pullM_getW, pullM_getW]
      exact hr3 _ w' (hargCtr j hj)
    · intro j hj w' n'
      rw [pullM_getArr, pullM_getArr, LstateM.getArr_setReg]
      exact LstateM.getArr_congr_larr hl3 _ _ _
  have hinv3 : ∀ j, j < invTys.length → (b3.reg.getW (τ (argName j)) 64).isSome := by
    intro j hj
    rw [hr3 _ 64 (hτ.invCtr j hj), LstateM.reg_setReg,
      LstateN.getW_setReg_other _ _ _ _ _ (hτ.invIdx j hj)]
    exact hinv j hj
  have hv3 : b3.reg.getW (loopCtr d) 64 = some (BitVec.ofNat 64 m) := (hc3 64).trans hcnt
  have hout : ∀ (s : LstateM) (t : Nat) (a : Fin n → BitVec w),
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) (pullM τ s)
        (tripValArrMN invs t a) → s.getArr out w n = some a := by
    intro s t a h
    have h1 := tripAgree_getArr_acc h
    rw [pullM_getArr] at h1
    rw [← hτ.acc]
    exact h1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hrun : runFBsL 1 blks b0 zf
        = some (b3.setLpc (b3.lpc + (flatFL [FBlock.straight B]).length + 6), true) := by
      rw [hblks, runFBsL_cons, runFB_straight, hseeds, Option.bind_some, runFBsL_cons,
        runFB_guarded_zeroTrip 1 _ _ _ _ b3 zf (by simpa using hv3), Option.bind_some,
        runFBsL_nil]
    obtain ⟨k, hk⟩ := flagNest_closed fn blks 1 b0 zf _ _ hpc hok hres hrun
    rw [hflat] at hk
    exact ⟨k, _, hk, hout b3 0 arr0 hAg3⟩
  · have hrunB := canonBodyRM_run update hupd hτ hcert absent regs hregs invs (b3.lpc + 3)
      (b3.setLpc (b3.lpc + 3)) arr0
      (by rw [pullM_setLpc]; exact StoreAgreesM.setLpc hAg3 _)
      (fun j hj => by rw [getW_setLpc]; exact hinv3 j hj)
      (BitVec.ofNat 64 m) (by rw [getW_setLpc]; exact hv3)
    obtain ⟨bfin, hbfin, hAgfin, _, hzfin⟩ := hrunB m
    have hsched := runFRegionF_of_schedule (loopCtr d) [FBlock.straight B] (b3.lpc + 3) 0 m
      (b3.setLpc (b3.lpc + 3)) hm bfin
      (by rw [runBoundedFBs_straight]; exact hbfin)
      (fun i _ him bi hbi => by
        obtain ⟨bi', hbi', _, _, hni⟩ := hrunB i
        rw [runBoundedFBs_straight] at hbi
        rw [hbi] at hbi'
        obtain rfl := Option.some.inj hbi'
        rw [condNZ_of_getW _ _ _ hni]
        exact decide_eq_true (ofNat_sub_ofNat_ne_zero m i hm64 him))
      (by rw [hzfin]; simp)
    rw [Nat.zero_add] at hsched
    have hne0 : (BitVec.ofNat 64 m == 0#64) = false := by
      have := ofNat_sub_ofNat_ne_zero m 0 hm64 hm
      simpa using this
    obtain ⟨bz, hbz, hbzl⟩ : ∃ bz,
        runFB m (.guarded d (d + 0x40000000) (loopCtr d) [.straight B]) b3 zf = some (bz, true)
          ∧ bz.larr = bfin.larr := by
      rw [runFB_guarded, hv3]
      simp only []
      rw [ite_eq_right (by simp [hne0]), hsched]
      exact ⟨_, rfl, rfl⟩
    have hrun : runFBsL m blks b0 zf = some (bz, true) := by
      rw [hblks, runFBsL_cons, runFB_straight, hseeds, Option.bind_some, runFBsL_cons, hbz,
        Option.bind_some, runFBsL_nil]
    obtain ⟨k, hk⟩ := flagNest_closed fn blks m b0 zf _ _ hpc hok hres hrun
    rw [hflat] at hk
    refine ⟨k, _, hk, ?_⟩
    show bz.getArr out w n = _
    rw [LstateM.getArr_congr_larr hbzl]
    exact hout bfin m _ hAgfin

/-! ## 6. The renamed export node is the canonicalised node -/

theorem renOperand_comp (ρ σ : String → String) (o : LOperand) :
    renOperand ρ (renOperand σ o) = renOperand (ρ ∘ σ) o := by
  cases o <;> rfl

theorem renLinstrR_comp (ρ σ : String → String) (i : LinstrR) :
    renLinstrR ρ (renLinstrR σ i) = renLinstrR (ρ ∘ σ) i := by
  have h : renOperand ρ ∘ renOperand σ = renOperand (ρ ∘ σ) := funext (renOperand_comp ρ σ)
  cases i <;> first
    | rfl
    | simp only [renLinstrR, List.map_map, h]

theorem renRM_comp (ρ σ : String → String) (i : LinstrRM) :
    renRM ρ (renRM σ i) = renRM (ρ ∘ σ) i := by
  obtain ⟨wire, tag⟩ := i
  show (renLinstrR ρ (renLinstrR σ wire), tag) = (renLinstrR (ρ ∘ σ) wire, tag)
  rw [renLinstrR_comp]

/-- The export's return register is the renaming of the model chain's. -/
theorem loopBodyWalkN_ret_eq_ren {σ : String → String} {nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (loopBodyWalkN d accReg (loopIdx d) invRegs (fun _ => none) com curDepth).2
      = σ (comRetReg (nInv + 2) argName com curDepth) := by
  induction com generalizing curDepth with
  | ret v =>
      simp only [loopBodyWalkN, comRetReg]
      rw [loopResolveVarN_eq_ren hσ curDepth v, resolveVar_isReg v]
      rfl
  | var e body ih =>
      simp only [loopBodyWalkN, comRetReg]
      exact ih (curDepth + 1)

/-- The guarded flag loop under a renaming. -/
theorem guardedFlagLoopLinstrRM_map_renRM (ρ : String → String) (top endL : LLabel)
    (nReg : String) (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body).map (renRM ρ)
      = guardedFlagLoopLinstrRM top endL (ρ nReg) (body.map (renRM ρ)) := by
  simp [guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge, renRM, renLinstrR,
    renOperand]

/-- The final head of a thread certificate has image `out`. -/
theorem ThreadCert.head_out (hτ : ThreadRen τ d nArgs S out) :
    ∀ (chain : List LinstrRM) (cd : Nat) (h hE : String), nArgs ≤ cd → τ h = out →
      ThreadCert τ nArgs S out chain cd h hE → τ hE = out := by
  intro chain
  induction chain with
  | nil =>
      intro cd h hE _ hh hc
      obtain rfl : h = hE := hc
      exact hh
  | cons i is ih =>
      intro cd h hE hcd hh hc
      rcases hc.2.2 with ⟨_, _, _, hrest⟩ | ⟨_, hS, hrest⟩
      · exact ih (cd + 1) h hE (by omega) hh hrest
      · exact ih (cd + 1) (regName cd) hE (by omega) (hτ.thr cd hcd hS) hrest

/-- The hypotheses on a renaming `ρ` of the export node's names: the accumulator
    register goes to `out`, and `out`, the loop index, the counter, the count
    register and the invariant base registers are fixed. -/
structure NodeRen (ρ : String → String) (d : Nat) (acc out c : String)
    (invRegs : List String) : Prop where
  /-- The accumulator register goes to `out`. -/
  accOut : ρ acc = out
  /-- `out` is fixed. -/
  outFix : ρ out = out
  /-- The loop index is fixed. -/
  idxFix : ρ (loopIdx d) = loopIdx d
  /-- The counter is fixed. -/
  ctrFix : ρ (loopCtr d) = loopCtr d
  /-- The count register is fixed. -/
  cntFix : ρ c = c
  /-- The invariant base registers are fixed. -/
  invFix : ∀ r ∈ invRegs, ρ r = r

/-- **The renamed looped segment is the canonicalised body.** For a renaming `ρ`
    of the node's names (`NodeRen`) that sends the export's return register to
    `out`, a loop renaming `σ` (`LoopRen`) and an update whose chain the export
    body walk renames (`ComRenOK`), the export's looped segment renamed by `ρ` is
    the canonicalised body at `τ = ρ ∘ σ`. -/
theorem forLoopBodyNRtRM_map_eq_canonBodyRM {w n : Nat} {σ ρ : String → String}
    {acc c : String} (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hcom : ComRenOK update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out) :
    (forLoopBodyNRtRM d acc update invOps (fun _ => none)).map (renRM ρ)
      = canonBodyRM (ρ ∘ σ) d out update
          ((loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
            (2 + invTys.length)).2 == acc) (invRegsOf invOps) := by
  have h1 : (loopBodyWalkNM d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
        (2 + invTys.length)).map (renRM ρ)
      = (straightOpsMem (invTys.length + 2) update (invTys.length + 2)).map
          (renRM (ρ ∘ σ)) := by
    rw [Nat.add_comm 2 invTys.length, loopBodyWalkNM_eq_ren hσ update hcom, List.map_map]
    exact List.map_congr_left (fun i _ => renRM_comp ρ σ i)
  have h2 : ∀ ret : String, ρ ret = out →
      (loopFeedbackRM acc ret).map (renRM ρ) = canonFeedback out (ret == acc) := by
    intro ret hr
    unfold loopFeedbackRM canonFeedback
    cases hra : (ret == acc) with
    | true => simp
    | false => simp [renRM, renLinstrR, renOperand, hρ.accOut, hr]
  have h3 : (loopAdvanceRM d).map (renRM ρ) = loopAdvanceRM d := by
    simp [loopAdvanceRM, renRM, renLinstrR, renOperand, hρ.idxFix, hρ.ctrFix]
  have h4 : (loopTouchRM d (invRegsOf invOps)).map (renRM ρ)
      = loopTouchRM d (invRegsOf invOps) := by
    unfold loopTouchRM
    rw [List.map_map]
    refine List.map_congr_left (fun r hr => ?_)
    simp [renRM, renLinstrR, renOperand, hρ.ctrFix, hρ.invFix r hr]
  unfold forLoopBodyNRtRM canonBodyRM
  simp only [List.map_append, h1, h2 _ hret, h3, h4, List.append_assoc]

/-- **The renamed export node is the canonicalised node.** Under the hypotheses of
    `forLoopBodyNRtRM_map_eq_canonBodyRM`, the typed export node seeded from
    `.reg out` with count operand `.reg c`, renamed by `ρ`, is `canonNodeRM` at
    `τ = ρ ∘ σ`. -/
theorem forLoopLcmdNRtRM_map_eq_canonNodeRM {w n : Nat} {σ ρ : String → String}
    {acc c : String} (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hcom : ComRenOK update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out) :
    (forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map (renRM ρ)
      = canonNodeRM (ρ ∘ σ) d out c update
          ((loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
            (2 + invTys.length)).2 == acc) (invRegsOf invOps) := by
  unfold forLoopLcmdNRtRM canonNodeRM
  rw [List.map_append, guardedFlagLoopLinstrRM_map_renRM, hρ.ctrFix,
    forLoopBodyNRtRM_map_eq_canonBodyRM invOps update hcom hσ hρ hret]
  congr 1
  simp [loopSeedsRM, canonSeedsRM, renRM, renLinstrR, renOperand, hρ.accOut, hρ.outFix,
    hρ.idxFix, hρ.ctrFix, hρ.cntFix]

/-- **Wire tie of the canonicalised aliased node.** When the alias map of the
    aliased export body is not empty and its resolution is the renaming `κ`, the
    wire projection of the typed export node renamed by `κ ∘ aliasRegName acc out`
    is the instruction stream of `canonicalizeMemrefThread` applied to
    `aliasRegBody acc out` of the export's `forLoopLcmdNRt`. -/
theorem forLoopLcmdNRtRM_canon_wire (κ : String → String) (acc out : String)
    (initOp countOp : LOperand) {accTy : JasminTy}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hne : (arrChainAlias (aliasRegBody acc out
      (forLoopLcmdNRt d acc initOp countOp update invOps immSlotMap))).isEmpty = false)
    (hκ : canonMemrefName (arrChainAlias (aliasRegBody acc out
      (forLoopLcmdNRt d acc initOp countOp update invOps immSlotMap))) = κ) :
    ((forLoopLcmdNRtRM d acc initOp countOp update invOps immSlotMap).map
        (renRM (κ ∘ aliasRegName acc out))).map Prod.fst
      = (canonicalizeMemrefThread (aliasRegBody acc out
          (forLoopLcmdNRt d acc initOp countOp update invOps immSlotMap))).map
            Linstr.li_i := by
  rw [canonicalizeMemrefThread_eq_renLcmd, ite_eq_right (by simp [hne]), hκ, renLcmd_wire,
    ← forLoopLcmdNRtRM_alias_wire, List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left (fun i _ => ?_)
  show (renRM (κ ∘ aliasRegName acc out) i).1 = renLinstrR κ (renRM (aliasRegName acc out) i).1
  rw [← renRM_comp]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
