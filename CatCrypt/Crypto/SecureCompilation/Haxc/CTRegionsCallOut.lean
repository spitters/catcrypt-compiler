/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegionsCall

@[expose] public section

set_option autoImplicit false

/-!
# The region analysis and the constant-time decision across a call with an out array

A calling body passes every array, the destination of an out callee included, as a pointer
region of the layout `σ`. This module extends the call arm of `RegionSep.memCheckX` to a
callee that also writes the `n` words at the address its register `rd` holds at entry
(`RegionSep.destAt`). The abstract effect of such a call is `RegionSep.transCall`: when the
register `rd` holds the entry value of the register of a pointer region of at least `n`
words (`RegionSep.outRegOK`), clause 3 of `σ.Regions` separates the destination from every
stack word of the frame range, so every stack-word fact of `transCall` survives.

The constant-time decision `AbiLayout.ctCheckRXO` takes an optional destination; at `none`
it is `AbiLayout.ctCheckRX`.

## Main results

* `RegionSep.transCall_sound_out`: the abstract effect of a call with an out array of a
  pointer region describes the state after the call, the callee and the return.
* `RegionSep.run_frameSepXO`, `RegionSep.memCheckXO_sound`: under a passing `memCheckXO`,
  every run under an oracle whose answers satisfy `CallPresO` for the destination is a run
  whose steps satisfy `FrameSep F` and whose call entries satisfy `RegionSep.OutClear`.
* `CalleeSpec.restrictEntry`: a specification of an interface is a specification of the
  interface restricted to the entry states satisfying a predicate.
* `Callee.haltsO_of_oracleRun`: a run with leakage under the traced oracle of a target is
  a halting run under the oracle of that target.
* `AbiLayout.ctCheckRXO_sound`: two runs of the linked program `p ++ shiftProg p.length q`
  for a caller `p` passing `ctCheckRXO … (some w)` and a callee `q` whose footprint lies in
  its frame or in the destination `destAt w.1 w.2` have equal leakage traces.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. Restricted interfaces and runs under a traced oracle -/

/-- The interface `c` restricted to the entry states satisfying `E`: the precondition and
    the footprint are conjoined with `E`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Callee.CalleeSig.restrictEntry
    (c : CalleeSig) (E : AState → Prop) : CalleeSig :=
  { c with pre := fun s => c.pre s ∧ E s, foot := fun s x => c.foot s x ∧ E s }

/-- **A specification of a restricted interface.** If `X` meets the interface `c`, it meets
    `c.restrictEntry E`: under the restricted precondition the restricted footprint is the
    footprint of `c`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Callee.CalleeSpec.restrictEntry
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) (E : AState → Prop) :
    CalleeSpec X (c.restrictEntry E) where
  halts s h := hX.halts s h.1
  rsp s t s' h := hX.rsp s t s' h.1
  keep s t s' h := hX.keep s t s' h.1
  frame s t s' h hr x hx := hX.frame s t s' h.1 hr x fun hf => hx ⟨hf, h.2⟩
  post s t s' h := hX.post s t s' h.1
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ := hX.ct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1

/-- **A run with leakage under the traced oracle of a target is a halting run under the
    oracle of that target**: the converse of `oracleRun_of_haltsO_oracleAt`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Callee.haltsO_of_oracleRun
    {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {tgt : Nat} {X : CalleeRun}
    {prog : List RInstr} {pc : Nat} {sa : AState} {t : List CTLeak} {sa' : AState}
    (h : OracleRun r ok (tracedAt tgt X) prog pc sa t sa') :
    HaltsO aMachine (oracleAt tgt X) prog pc sa sa' :=
  h.haltsO.mono fun _ _ _ ⟨tr, ht, hx⟩ => ⟨ht, tr, hx⟩

namespace RegionSep

/-! ## 2. The destination of an out call -/

/-- The register `rd` is not `%rsp` and holds, by the facts of `m`, the entry value of the
    register of a pointer region of `σ` with at least `n` words. -/
def outRegOK (σ : AbiLayout) (m : MA) (rd : String) (n : Nat) : Bool :=
  rd != "%rsp" &&
    m.ent.any fun p => p.1 == rd && σ.regions.any fun q => q.1 == p.2 && decide (n ≤ q.2)

/-- The bytes of the `n` destination words from the address the register `rd` holds in the
    callee's entry state. -/
def destAt (rd : String) (n : Nat) : AState → BitVec 64 → Prop :=
  fun s x => ∃ j < n, InRange8 (s.regs rd + BitVec.ofNat 64 (8 * j)) x

/-- The words at the offsets `Q` above the stack register of `s` lie outside the destination
    `destAt rd n s`. -/
def OutClear (rd : String) (n : Nat) (Q : List Int) (s : AState) : Prop :=
  ∀ q ∈ Q, ∀ x, InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x → ¬ destAt rd n s x

section Soundness

variable {σ : AbiLayout} {s0 : AState}

/-- A stack word of the frame range lies outside the destination of a call whose register
    passes `outRegOK`. -/
theorem not_destAt_of_outRegOK {m : MA} {sa : AState} {rd : String} {n k : Nat}
    (hR : σ.Regions s0) (hI : Inv σ s0 m sa) (hok : outRegOK σ m rd n = true) {o : Int}
    (hlo : σ.frameLo ≤ o) (hhi : o ≤ σ.frameHi) {x : BitVec 64}
    (hx : InRange8 (s0.regs "%rsp" + BitVec.ofInt 64 o) x) :
    ¬ destAt rd n (runBlockA sa (callOps k)) x := by
  rintro ⟨j, hj, hjx⟩
  simp only [outRegOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  obtain ⟨hne, ⟨rd', x0⟩, hmem, rfl, q, hq, hqx, hle⟩ := hok
  have hreg : (runBlockA sa (callOps k)).regs rd' = s0.regs q.1 := by
    rw [callOps_regs _ _ hne, hI.ent _ hmem, hqx]
  rw [hreg] at hjx
  obtain ⟨h1, h2⟩ := hR.2.2.1 q hq j (by omega) o hlo hhi
  unfold InRange8 at hx hjx
  simp only [BitVec.toNat_sub] at h1 h2 hx hjx
  have := x.isLt
  have := (s0.regs "%rsp" + BitVec.ofInt 64 o).isLt
  have := (s0.regs q.1 + BitVec.ofNat 64 (8 * j)).isLt
  omega

/-- **Soundness of the abstract effect of a call with an out array of a pointer region.**
    If `m` describes the caller's state `sa`, the register `rd` passes `outRegOK σ m rd n`,
    and the callee entered after the stack operations of the call returns in `sc` with
    `CallPresO clob G (destAt rd n)`, then `transCall G clob m` describes the state after
    the return. -/
theorem transCall_sound_out {G : Nat} {clob : String → Bool} {m : MA} {sa sc : AState}
    {k : Nat} {rd : String} {n : Nat} (hR : σ.Regions s0) (hI : Inv σ s0 m sa)
    (hok : outRegOK σ m rd n = true)
    (hP : CallPresO clob G (destAt rd n) (runBlockA sa (callOps k)) sc) :
    Inv σ s0 (transCall G clob m) (runBlockA sc retOps) := by
  set sc0 := runBlockA sa (callOps k) with hsc0
  have hsp : (runBlockA sc retOps).regs "%rsp" = sa.regs "%rsp" := by
    rw [retOps_rsp, hP.rsp, hsc0, callOps_rsp, ofInt_add_assoc]
    simp
  have hreg : ∀ x, clob x = false → (runBlockA sc retOps).regs x = sa.regs x := by
    intro x hx
    by_cases hr : x = "%rsp"
    · subst hr; exact hsp
    · rw [retOps_regs _ hr, hP.keep x hx, hsc0, callOps_regs _ _ hr]
  have hreg' : ∀ x, (!clob x) = true → (runBlockA sc retOps).regs x = sa.regs x :=
    fun x hx => hreg x (by simpa using hx)
  have hword : ∀ e, keptSlot G m.sp e = true → inW σ e = true →
      wdAt s0 (runBlockA sc retOps) e = wdAt s0 sa e := by
    intro e hk hin
    simp only [keptSlot, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨h1, h2⟩ := hk
    simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at hin
    have hrsp0 : sc0.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
        + BitVec.ofInt 64 (-8) := by
      rw [hsc0, callOps_rsp, hI.sp]
    have haddr : s0.regs "%rsp" + BitVec.ofInt 64 e
        = sc0.regs "%rsp" + BitVec.ofInt 64 (e - m.sp + 8) := by
      rw [hrsp0, ofInt_add_assoc, ofInt_add_assoc]
      congr 2
      omega
    simp only [wdAt]
    rw [retOps_mem, haddr]
    have hm : ∀ x, InRange8 (sc0.regs "%rsp" + BitVec.ofInt 64 (e - m.sp + 8)) x →
        sc.mem x = sc0.mem x := fun x hx =>
      hP.frame x (not_inFrame_of_inRange8 (by omega) (by omega) hx)
        (not_destAt_of_outRegOK hR hI hok hin.1 hin.2 (by rw [haddr]; exact hx))
    rw [read64_congr hm, ← haddr, hsc0, callOps_read64]
    rw [hI.sp, ofInt_add_assoc]
    exact disjoint8_add_ofInt (s0.regs "%rsp") (m.sp + -8) e (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.w.frame hreg' hword⟩
  · rw [hsp]; exact hI.sp
  · intro p hp
    simp only [transCall, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.ent p hp.1
  · intro r hr
    simp only [transCall, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.zero r hr.1
  · intro e he
    simp only [transCall, List.mem_filter, keptSlot, Bool.and_eq_true,
      decide_eq_true_eq] at he
    obtain ⟨he, h1, h2⟩ := he
    have hin := (hI.slot e he).1
    simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at hin
    refine ⟨(hI.slot e he).1, ?_⟩
    have hrsp0 : sc0.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
        + BitVec.ofInt 64 (-8) := by
      rw [hsc0, callOps_rsp, hI.sp]
    have haddr : s0.regs "%rsp" + BitVec.ofInt 64 e.1
        = sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8) := by
      rw [hrsp0, ofInt_add_assoc, ofInt_add_assoc]
      congr 2
      omega
    rw [retOps_mem, haddr]
    have hm : ∀ x, InRange8 (sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8)) x →
        sc.mem x = sc0.mem x := fun x hx =>
      hP.frame x (not_inFrame_of_inRange8 (by omega) (by omega) hx)
        (not_destAt_of_outRegOK hR hI hok hin.1 hin.2 (by rw [haddr]; exact hx))
    rw [read64_congr hm, ← haddr, hsc0, callOps_read64]
    · exact (hI.slot e he).2
    · rw [hI.sp, ofInt_add_assoc]
      exact disjoint8_add_ofInt (s0.regs "%rsp") (m.sp + -8) e.1 (by omega) (by omega)
  · intro f hf
    simp only [transCall, List.mem_filter, Bool.and_eq_true] at hf
    rw [hreg' _ hf.2.1, hreg' _ hf.2.2]; exact hI.le f hf.1
  · intro r hr
    simp only [transCall, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.nz r hr.1
  · intro c hc
    simp [transCall] at hc
  · intro p hp
    simp only [transCall, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.cst p hp.1

/-- At a call entry after a caller state described by `m`, with `frameOK σ F m` and a
    register passing `outRegOK`, the callee words at the offsets `F.map (· + 8)` lie outside
    the destination. -/
theorem outClear_of_frameOK {m : MA} {sa : AState} {F : List Int} {rd : String} {n k : Nat}
    (hR : σ.Regions s0) (hI : Inv σ s0 m sa) (hok : outRegOK σ m rd n = true)
    (hF : frameOK σ F m = true) :
    OutClear rd n (F.map (· + 8)) (runBlockA sa (callOps k)) := by
  intro q hq x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hq
  have hw := List.all_eq_true.mp hF o ho
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at hw
  have haddr : (runBlockA sa (callOps k)).regs "%rsp" + BitVec.ofInt 64 (o + 8)
      = s0.regs "%rsp" + BitVec.ofInt 64 (m.sp + o) := by
    grind only [callOps_rsp, BitVec.ofInt_add, Inv.sp]
  exact not_destAt_of_outRegOK hR hI hok hw.1 hw.2 (haddr ▸ hx)

end Soundness

/-! ## 3. The certificate check with an out call arm -/

/-- The check at index `pc` for a caller whose calls write the destination of `w.2` words
    from the register `w.1`: a `call` passes when the certificate assigns the next index an
    abstract state below `transCall G clob m`, the destination register passes `outRegOK`
    and the frame words lie in the frame range; the other instructions are checked by
    `checkAtM`. -/
def checkAtMXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (w : String × Nat)
    (F : List Int) (prog : List RInstr) (M : Array (Option MA)) (pc : Nat) : Bool :=
  match M.getD pc none with
  | none => true
  | some m =>
    match prog[pc]? with
    | some (.call _) => succOkM M (pc + 1) (transCall G clob m)
        && outRegOK σ m w.1 w.2 && frameOK σ F m
    | _ => checkAtM σ F prog M pc

/-- **The certificate check with an out call arm**: the entry index is below `init σ` and
    every index passes `checkAtMXO`. -/
def memCheckXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (w : String × Nat)
    (F : List Int) (prog : List RInstr) (M : Array (Option MA)) : Bool :=
  succOkM M 0 (init σ) && (List.range prog.length).all (checkAtMXO σ clob G w F prog M)

section Soundness

variable {σ : AbiLayout} {s0 : AState}

/-- **Every step of a run under an oracle with an out call satisfies the separation
    condition.** Under a passing `checkAtMXO` at every index, a run under an oracle whose
    answers satisfy `CallPresO clob G (destAt w.1 w.2)`, from an index whose abstract state
    describes the current state, for an entry state satisfying `σ.Regions`, is a run whose
    steps satisfy `FrameSep F` and whose call entries satisfy
    `OutClear w.1 w.2 (F.map (· + 8))`. -/
theorem run_frameSepXO {r : DoitRegime} {clob : String → Bool} {G : Nat} {w : String × Nat}
    {F : List Int} {prog : List RInstr} {M : Array (Option MA)} {O : Nat → CalleeRun}
    (hc : (List.range prog.length).all (checkAtMXO σ clob G w F prog M) = true)
    (hR : σ.Regions s0)
    (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPresO clob G (destAt w.1 w.2) sc0 sc)
    {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : OracleRun r (fun _ _ => True) O prog pc s t s') :
    ∀ m, M.getD pc none = some m → Inv σ s0 m s →
      OracleRun r (FrameSep F)
        (fun tg sc0 tc sc => O tg sc0 tc sc ∧ OutClear w.1 w.2 (F.map (· + 8)) sc0)
        prog pc s t s' := by
  have hat : ∀ {pc : Nat} {x : RInstr}, prog[pc]? = some x →
      checkAtMXO σ clob G w F prog M pc = true :=
    fun hx => List.all_eq_true.mp hc _
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hx).1)
  induction h with
  | ret h => exact fun _ _ _ => .ret h
  | @op pc s i t s' h _ _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtMXO, hm, h, checkAtM, Bool.and_eq_true] at hck
    obtain ⟨hs, ht⟩ := hck
    split at ht
    · rename_i o ho
      obtain ⟨b, hb, hle⟩ := succOkM_spec ht
      have hcell : cellAddrOK σ m i = true := by
        simp only [safeW, Bool.and_eq_true] at hs
        exact hs.1
      exact .op h (frameSep_of_safeW hR hI hs)
        (ih b hb (Inv.of_leM hle (trans_sound hR hI hcell ho)))
    · simp at ht
  | @jcc pc s cc tgt c t s' h hcc _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtMXO, hm, h, checkAtM, hcc, Bool.and_eq_true] at hck
    refine .jcc h hcc ?_
    cases hcb : s.view.condB c
    · obtain ⟨b, hb, hle⟩ := succOkM_spec hck.2
      have := ih b (by simpa [hcb] using hb) (Inv.of_leM hle (jccOut_sound hI hcb))
      simpa [hcb] using this
    · obtain ⟨b, hb, hle⟩ := succOkM_spec hck.1
      have := ih b (by simpa [hcb] using hb) (Inv.of_leM hle (jccOut_sound hI hcb))
      simpa [hcb] using this
  | @stack pc s ri ops t s' h hops _ _ _ =>
    intro m hm _
    have hck := hat h
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq] at hops <;>
      simp [checkAtMXO, checkAtM, hm, h] at hck
  | @call pc tgt sa sc tc tr sa' h _ hcall _ _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtMXO, hm, h, Bool.and_eq_true] at hck
    obtain ⟨⟨hs, hok⟩, hF⟩ := hck
    obtain ⟨b, hb, hle⟩ := succOkM_spec hs
    exact .call h (blockOk_frameSep_callOps F sa (pc + 1))
      ⟨hcall, outClear_of_frameOK hR hI hok hF⟩ (blockOk_frameSep_retOps F sc)
      (ih b hb (Inv.of_leM hle (transCall_sound_out hR hI hok (hO _ _ _ _ hcall))))

/-- **Soundness of the certificate check with an out call arm.** Under a passing
    `memCheckXO σ clob G w F prog M`, every run of `prog` from index `0` and an entry state
    satisfying `σ.Regions`, under an oracle whose answers satisfy
    `CallPresO clob G (destAt w.1 w.2)`, is a run whose steps satisfy `FrameSep F` and whose
    call entries satisfy `OutClear w.1 w.2 (F.map (· + 8))`. -/
theorem memCheckXO_sound {r : DoitRegime} {clob : String → Bool} {G : Nat}
    {w : String × Nat} {F : List Int} {prog : List RInstr} {M : Array (Option MA)}
    {O : Nat → CalleeRun} (hc : memCheckXO σ clob G w F prog M = true) (hR : σ.Regions s0)
    (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPresO clob G (destAt w.1 w.2) sc0 sc)
    {t : List CTLeak} {s' : AState} (h : OracleRun r (fun _ _ => True) O prog 0 s0 t s') :
    OracleRun r (FrameSep F)
      (fun tg sc0 tc sc => O tg sc0 tc sc ∧ OutClear w.1 w.2 (F.map (· + 8)) sc0)
      prog 0 s0 t s' := by
  simp only [memCheckXO, Bool.and_eq_true] at hc
  obtain ⟨b, hb, hle⟩ := succOkM_spec hc.1
  exact run_frameSepXO hc.2 hR hO h b hb (Inv.of_leM hle (inv_init hR))

end Soundness

/-- The stack offsets of the certificate `M` at the `call` indices. -/
def callSps (prog : List RInstr) (M : Array (Option MA)) : List Int :=
  (List.range prog.length).filterMap fun pc =>
    match prog[pc]?, M.getD pc none with
    | some (RInstr.call _), some m => some m.sp
    | _, _ => none

end RegionSep

namespace AbiLayout

open RegionSep

/-- The trimmed certificate of the gate with an out call arm on `prog`: frame words are
    kept when they lie in the frame range at the stack offsets of the stores through a
    base other than `%rsp` and of the calls. -/
def ctCertRXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    List (Option PubA) :=
  trimCertL σ (storeSps prog (inferMX σ clob G prog) ++ callSps prog (inferMX σ clob G prog))
    (inferX clob G prog σ.pubAS)

/-- The frame words of the trimmed certificate with an out call arm. -/
def ctFrameRXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    List Int :=
  (certCells (σ.ctCertRXO clob G prog)).eraseDups

/-- **The constant-time decision with a call of a linked callee and an optional
    destination.** At `none` it is `ctCheckRX`. At `some w`, for a callee writing the `w.2`
    words from the register `w.1`, the trimmed certificate `ctCertRXO` assigns the entry a
    set below `σ.pubAS`, the caller passes `checkCertX` at the external entry
    `prog.length`, and the region check with the out call arm passes for the frame words. -/
def ctCheckRXO (σ : AbiLayout) (clob : String → Bool) (pubRegs : List String) (G : Nat) :
    Option (String × Nat) → List RInstr → Bool
  | none, prog => σ.ctCheckRX clob pubRegs G prog
  | some w, prog =>
    succOk (σ.ctCertRXO clob G prog) 0 σ.pubAS
      && checkCertX ctRegime (σ.ctFrameRXO clob G prog) prog.length pubRegs
        (keptRegsX clob (σ.ctCertRXO clob G prog)) (keptCellsX G (σ.ctCertRXO clob G prog))
        prog (σ.ctCertRXO clob G prog)
      && memCheckXO σ clob G w (σ.ctFrameRXO clob G prog) prog (inferMX σ clob G prog)

/-- The unfolding lemma of `ctCheckRXO` at no destination. -/
theorem ctCheckRXO_none (σ : AbiLayout) (clob : String → Bool) (pubRegs : List String)
    (G : Nat) (p : List RInstr) :
    σ.ctCheckRXO clob pubRegs G none p = σ.ctCheckRX clob pubRegs G p := rfl

/-- **Soundness of `ctCheckRXO` at a destination.** Let `q` be a block without `call` whose
    leaky runs meet the interface `c`, with clobber set inside `clob`, footprint in the `G`
    bytes below the entry stack register or in the destination `destAt w.1 w.2`, and
    agreement on `callPub pubRegs` between entry states satisfying the precondition giving
    `c.pub`. Let the caller `p` pass `σ.ctCheckRXO clob pubRegs G (some w)` and halt under
    the guarded oracle of `q` from two entry states satisfying `σ.Regions` and agreeing on
    the public data of `σ`. Then every two runs with leakage of `p ++ shiftProg p.length q`
    from these states have equal traces. -/
theorem ctCheckRXO_sound {σ : AbiLayout} {clob : String → Bool} {pubRegs : List String}
    {G : Nat} {w : String × Nat} {p q : List RInstr}
    (h : σ.ctCheckRXO clob pubRegs G (some w) p = true)
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf ctRegime q) c)
    (hclob : ∀ x, clob x = false → c.clob x = false)
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x ∨ destAt w.1 w.2 s x)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hag : σ.PubAgree s₁ s₂) (hR₁ : σ.Regions s₁)
    (hR₂ : σ.Regions s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL ctRegime ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  simp only [ctCheckRXO, Bool.and_eq_true] at h
  obtain ⟨⟨h0, hc⟩, hm⟩ := h
  set F := σ.ctFrameRXO clob G p with hFdef
  set A := σ.ctCertRXO clob G p with hAdef
  set E := OutClear w.1 w.2 (F.map (· + 8)) with hEdef
  set Y := runOf ctRegime q
  have hO : ∀ tg sc0 tc sc, tracedAt p.length (guarded c Y) tg sc0 tc sc →
      CallPresO clob G (destAt w.1 w.2) sc0 sc :=
    fun _ _ _ _ ho => callPresO_of_guarded hX hclob hfoot ho.2
  have hdown : ∀ tg s tr sc, tracedAt p.length (guarded (c.restrictEntry E) Y) tg s tr sc →
      tracedAt p.length (guarded c Y) tg s tr sc :=
    fun _ _ _ _ ho => ⟨ho.1, ho.2.1.1, ho.2.2⟩
  have hup : ∀ tg s tr sc, (tracedAt p.length (guarded c Y) tg s tr sc ∧ E s) →
      tracedAt p.length (guarded (c.restrictEntry E) Y) tg s tr sc :=
    fun _ _ _ _ ho => ⟨ho.1.1, ⟨ho.1.2.1, ho.2⟩, ho.1.2.2⟩
  have hsep : ∀ {s0 : AState} {t : List CTLeak} {s' : AState}, σ.Regions s0 →
      OracleRun ctRegime (fun _ _ => True) (tracedAt p.length (guarded (c.restrictEntry E) Y))
        p 0 s0 t s' →
      OracleRun ctRegime (FrameSep F) (tracedAt p.length (guarded (c.restrictEntry E) Y))
        p 0 s0 t s' :=
    fun hR ho => (memCheckXO_sound hm hR hO (ho.mono_oracle hdown)).mono_oracle hup
  have hH : ∀ {s0 s' : AState}, σ.Regions s0 →
      HaltsO aMachine (oracleAt p.length (guarded c Y)) p 0 s0 s' →
      HaltsO aMachine (oracleAt p.length (guarded (c.restrictEntry E) Y)) p 0 s0 s' := by
    intro s0 s' hR hh
    obtain ⟨t, ho⟩ := oracleRun_of_haltsO_oracleAt ctRegime hh
    exact haltsO_of_oracleRun ((memCheckXO_sound hm hR hO ho).mono_oracle hup)
  have hR : ∀ x ∈ keptRegsX clob A, (c.restrictEntry E).clob x = false := by
    intro x hx
    simp only [keptRegsX, List.mem_filter, Bool.not_eq_true'] at hx
    exact hclob x hx.2
  have hQ : ∀ q ∈ keptCellsX G A, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64 := by
    intro q hq
    simp only [keptCellsX, qOk, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  have hQF : ∀ q ∈ keptCellsX G A, q ∈ F.map (· + 8) := by
    intro q hq
    simp only [keptCellsX, List.mem_filter, List.mem_map] at hq
    obtain ⟨⟨a, ha, rfl⟩, _⟩ := hq
    exact List.mem_map.mpr ⟨a, by rw [hFdef, ctFrameRXO, List.mem_eraseDups]; exact ha, rfl⟩
  have hQO : ∀ s, ∀ q ∈ keptCellsX G A, ∀ x,
      InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x → ¬ (destAt w.1 w.2 s x ∧ E s) :=
    fun _ q hq x hx hd => hd.2 q (hQF q hq) x hx hd.1
  obtain ⟨b, hb, hle⟩ := succOk_spec h0
  exact linkedRunX_trace_eq_out (O := fun s x => destAt w.1 w.2 s x ∧ E s) hq
    (hX.restrictEntry E) hc hR
    (fun s x hf => (hfoot s x hf.1).imp id fun hd => ⟨hd, hf.2⟩) hQ hQO
    (fun s₁ s₂ h₁ h₂ hp => hpub s₁ s₂ h₁.1 h₂.1 hp)
    ⟨b, hb, PubA.agree_of_le hle (pubAS_agree hag hR₁ hR₂)⟩ (hH hR₁ h₁) (hH hR₂ h₂)
    (fun _ _ ho => hsep hR₁ ho) (fun _ _ ho => hsep hR₂ ho) hr₁ hr₂

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc
