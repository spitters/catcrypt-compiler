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
region of the layout `σ`. A callee may also write the `n` words at the address its register
`rd` holds at entry (`RegionSep.destAt`). The abstract effect of such a call is
`RegionSep.transCall`: when the register `rd` holds the entry value of the register of a
pointer region of at least `n` words (`RegionSep.outRegOK`), clause 3 of `σ.Regions` separates
the destination from every stack word of the frame range, so every stack-word fact of
`transCall` survives.

The certificate check `RegionSep.memCheckXT` and the constant-time decision
`AbiLayout.ctCheckRXT` read the target of a call: a map `w` gives its destination and a map
`ext` its public argument registers, with one clobber set and one frame for all targets.
`AbiLayout.ctCheckRXO` and `AbiLayout.ctCheckRX` are `ctCheckRXT` at one entry and a constant
destination.

## Main results

* `RegionSep.transCall_sound_out`: the abstract effect of a call with an out array of a
  pointer region describes the state after the call, the callee and the return.
* `RegionSep.run_frameSepXT`, `RegionSep.memCheckXT_sound`: under a passing `memCheckXT`,
  every run under an oracle whose answers satisfy `CallPresT` is a run whose steps satisfy
  `FrameSep F` and whose call entries satisfy `RegionSep.OutClearT`.
* `RegionSep.memCheckXO_sound`, `RegionSep.memCheckX_sound`: the same at a constant destination
  and at no destination.
* `CalleeSpec.restrictEntry`: a specification of an interface is a specification of the
  interface restricted to the entry states satisfying a predicate.
* `Callee.haltsO_of_oracleRun`: a run with leakage under the traced oracle of a target is
  a halting run under the oracle of that target.
* `AbiLayout.ctCheckRXT_sound`: two runs of the linked program `p ++ shiftProg p.length B` for
  a caller `p` passing `ctCheckRXT` and callees at injective entries of `B`, each with its
  footprint in its frame or its destination, have equal leakage traces.
* `AbiLayout.ctCheckRX_sound`, `AbiLayout.ctCheckRXO_sound`: the same at one callee `q`, without
  a destination and at the destination `destAt w.1 w.2`.
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

/-- The check at index `pc` for a caller whose call to a target `t` writes, when
    `w t = some d`, the destination of `d.2` words from the register `d.1`. A `call t` passes
    when the certificate assigns the next index an abstract state below
    `transCall G clob m` and, at a destination, the destination register passes `outRegOK`
    and the frame words lie in the frame range; the other instructions are checked by
    `checkAtM`. -/
def checkAtMXT (σ : AbiLayout) (clob : String → Bool) (G : Nat)
    (w : Nat → Option (String × Nat)) (F : List Int) (prog : List RInstr)
    (M : Array (Option MA)) (pc : Nat) : Bool :=
  match M.getD pc none with
  | none => true
  | some m =>
    match prog[pc]? with
    | some (.call t) =>
        match w t with
        | some d => succOkM M (pc + 1) (transCall G clob m)
            && outRegOK σ m d.1 d.2 && frameOK σ F m
        | none => succOkM M (pc + 1) (transCall G clob m)
    | _ => checkAtM σ F prog M pc

/-- **The certificate check at a map of destinations**: the entry index is below `init σ` and
    every index passes `checkAtMXT`. -/
def memCheckXT (σ : AbiLayout) (clob : String → Bool) (G : Nat)
    (w : Nat → Option (String × Nat)) (F : List Int) (prog : List RInstr)
    (M : Array (Option MA)) : Bool :=
  succOkM M 0 (init σ) && (List.range prog.length).all (checkAtMXT σ clob G w F prog M)

/-- The check at index `pc` for a caller whose calls have no destination. -/
abbrev checkAtMX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (F : List Int)
    (prog : List RInstr) (M : Array (Option MA)) : Nat → Bool :=
  checkAtMXT σ clob G (fun _ => none) F prog M

/-- The certificate check for a caller whose calls have no destination. -/
abbrev memCheckX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (F : List Int)
    (prog : List RInstr) (M : Array (Option MA)) : Bool :=
  memCheckXT σ clob G (fun _ => none) F prog M

/-- The check at index `pc` for a caller whose calls all write the destination of `w.2` words
    from the register `w.1`. -/
abbrev checkAtMXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (w : String × Nat)
    (F : List Int) (prog : List RInstr) (M : Array (Option MA)) : Nat → Bool :=
  checkAtMXT σ clob G (fun _ => some w) F prog M

/-- The certificate check for a caller whose calls all write the destination `w`. -/
abbrev memCheckXO (σ : AbiLayout) (clob : String → Bool) (G : Nat) (w : String × Nat)
    (F : List Int) (prog : List RInstr) (M : Array (Option MA)) : Bool :=
  memCheckXT σ clob G (fun _ => some w) F prog M

/-- What an answer of the oracle at the target `tg` must satisfy: `CallPresO` for the
    destination of `tg`, and `CallPres` at a target without a destination. -/
def CallPresT (clob : String → Bool) (G : Nat) (w : Nat → Option (String × Nat)) (tg : Nat)
    (sc0 sc : AState) : Prop :=
  match w tg with
  | some d => CallPresO clob G (destAt d.1 d.2) sc0 sc
  | none => CallPres clob G sc0 sc

/-- A call entry at the target `tg`: the words at the offsets `F.map (· + 8)` lie outside the
    destination of `tg`, and no condition holds at a target without a destination. -/
def OutClearT (w : Nat → Option (String × Nat)) (F : List Int) (tg : Nat) (s : AState) : Prop :=
  match w tg with
  | some d => OutClear d.1 d.2 (F.map (· + 8)) s
  | none => True

section Soundness

variable {σ : AbiLayout} {s0 : AState}

/-- **Every step of a run under an oracle at a map of destinations satisfies the separation
    condition.** Under a passing `checkAtMXT` at every index, a run under an oracle whose
    answers satisfy `CallPresT clob G w`, from an index whose abstract state describes the
    current state, for an entry state satisfying `σ.Regions`, is a run whose steps satisfy
    `FrameSep F` and whose call entries satisfy `OutClearT w F`. -/
theorem run_frameSepXT {r : DoitRegime} {clob : String → Bool} {G : Nat}
    {w : Nat → Option (String × Nat)}
    {F : List Int} {prog : List RInstr} {M : Array (Option MA)} {O : Nat → CalleeRun}
    (hc : (List.range prog.length).all (checkAtMXT σ clob G w F prog M) = true)
    (hR : σ.Regions s0)
    (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPresT clob G w tg sc0 sc)
    {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : OracleRun r (fun _ _ => True) O prog pc s t s') :
    ∀ m, M.getD pc none = some m → Inv σ s0 m s →
      OracleRun r (FrameSep F)
        (fun tg sc0 tc sc => O tg sc0 tc sc ∧ OutClearT w F tg sc0)
        prog pc s t s' := by
  have hat : ∀ {pc : Nat} {x : RInstr}, prog[pc]? = some x →
      checkAtMXT σ clob G w F prog M pc = true :=
    fun hx => List.all_eq_true.mp hc _
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hx).1)
  induction h with
  | ret h => exact fun _ _ _ => .ret h
  | @op pc s i t s' h _ _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtMXT, hm, h, checkAtM, Bool.and_eq_true] at hck
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
    simp only [checkAtMXT, hm, h, checkAtM, hcc, Bool.and_eq_true] at hck
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
      simp [checkAtMXT, checkAtM, hm, h] at hck
  | @call pc tgt sa sc tc tr sa' h _ hcall _ _ ih =>
    intro m hm hI
    have hck := hat h
    simp only [checkAtMXT, hm, h] at hck
    have hP := hO _ _ _ _ hcall
    cases hw : w tgt with
    | none =>
      simp only [hw] at hck
      obtain ⟨b, hb, hle⟩ := succOkM_spec hck
      simp only [CallPresT, hw] at hP
      exact .call h (blockOk_frameSep_callOps F sa (pc + 1))
        ⟨hcall, by simp only [OutClearT, hw]⟩ (blockOk_frameSep_retOps F sc)
        (ih b hb (Inv.of_leM hle (transCall_sound hI hP)))
    | some d =>
      simp only [hw, Bool.and_eq_true] at hck
      obtain ⟨⟨hs, hok⟩, hF⟩ := hck
      obtain ⟨b, hb, hle⟩ := succOkM_spec hs
      simp only [CallPresT, hw] at hP
      exact .call h (blockOk_frameSep_callOps F sa (pc + 1))
        ⟨hcall, by simpa only [OutClearT, hw] using outClear_of_frameOK hR hI hok hF⟩
        (blockOk_frameSep_retOps F sc)
        (ih b hb (Inv.of_leM hle (transCall_sound_out hR hI hok hP)))

/-- **Soundness of the certificate check at a map of destinations.** Under a passing
    `memCheckXT σ clob G w F prog M`, every run of `prog` from index `0` and an entry state
    satisfying `σ.Regions`, under an oracle whose answers satisfy `CallPresT clob G w`, is a
    run whose steps satisfy `FrameSep F` and whose call entries satisfy `OutClearT w F`. -/
theorem memCheckXT_sound {r : DoitRegime} {clob : String → Bool} {G : Nat}
    {w : Nat → Option (String × Nat)} {F : List Int} {prog : List RInstr}
    {M : Array (Option MA)} {O : Nat → CalleeRun} (hc : memCheckXT σ clob G w F prog M = true)
    (hR : σ.Regions s0) (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPresT clob G w tg sc0 sc)
    {t : List CTLeak} {s' : AState} (h : OracleRun r (fun _ _ => True) O prog 0 s0 t s') :
    OracleRun r (FrameSep F)
      (fun tg sc0 tc sc => O tg sc0 tc sc ∧ OutClearT w F tg sc0)
      prog 0 s0 t s' := by
  simp only [memCheckXT, Bool.and_eq_true] at hc
  obtain ⟨b, hb, hle⟩ := succOkM_spec hc.1
  exact run_frameSepXT hc.2 hR hO h b hb (Inv.of_leM hle (inv_init hR))

/-- **Every step of a run under an oracle with an out call satisfies the separation
    condition**: `run_frameSepXT` at the constant destination `w`. -/
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
        prog pc s t s' :=
  run_frameSepXT (w := fun _ => some w) hc hR hO h

/-- **Soundness of the certificate check with an out call arm**: `memCheckXT_sound` at the
    constant destination `w`. -/
theorem memCheckXO_sound {r : DoitRegime} {clob : String → Bool} {G : Nat}
    {w : String × Nat} {F : List Int} {prog : List RInstr} {M : Array (Option MA)}
    {O : Nat → CalleeRun} (hc : memCheckXO σ clob G w F prog M = true) (hR : σ.Regions s0)
    (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPresO clob G (destAt w.1 w.2) sc0 sc)
    {t : List CTLeak} {s' : AState} (h : OracleRun r (fun _ _ => True) O prog 0 s0 t s') :
    OracleRun r (FrameSep F)
      (fun tg sc0 tc sc => O tg sc0 tc sc ∧ OutClear w.1 w.2 (F.map (· + 8)) sc0)
      prog 0 s0 t s' :=
  memCheckXT_sound (w := fun _ => some w) hc hR hO h

/-- **Every step of a run under an oracle satisfies the separation condition**:
    `run_frameSepXT` at no destination. -/
theorem run_frameSepX {r : DoitRegime} {clob : String → Bool} {G : Nat} {F : List Int}
    {prog : List RInstr} {M : Array (Option MA)} {O : Nat → CalleeRun}
    (hc : (List.range prog.length).all (checkAtMX σ clob G F prog M) = true)
    (hR : σ.Regions s0) (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPres clob G sc0 sc)
    {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState}
    (h : OracleRun r (fun _ _ => True) O prog pc s t s') :
    ∀ m, M.getD pc none = some m → Inv σ s0 m s → OracleRun r (FrameSep F) O prog pc s t s' :=
  fun m hm hI => (run_frameSepXT (w := fun _ => none) hc hR hO h m hm hI).mono_oracle
    fun _ _ _ _ ho => ho.1

/-- **Soundness of the certificate check with a call arm**: `memCheckXT_sound` at no
    destination. -/
theorem memCheckX_sound {r : DoitRegime} {clob : String → Bool} {G : Nat} {F : List Int}
    {prog : List RInstr} {M : Array (Option MA)} {O : Nat → CalleeRun}
    (hc : memCheckX σ clob G F prog M = true) (hR : σ.Regions s0)
    (hO : ∀ tg sc0 tc sc, O tg sc0 tc sc → CallPres clob G sc0 sc)
    {t : List CTLeak} {s' : AState} (h : OracleRun r (fun _ _ => True) O prog 0 s0 t s') :
    OracleRun r (FrameSep F) O prog 0 s0 t s' :=
  (memCheckXT_sound (w := fun _ => none) hc hR hO h).mono_oracle fun _ _ _ _ ho => ho.1

end Soundness

/-- The stack offsets of the certificate `M` at the `call` indices whose target has a
    destination under `w`. -/
def callSpsT (w : Nat → Option (String × Nat)) (prog : List RInstr) (M : Array (Option MA)) :
    List Int :=
  (List.range prog.length).filterMap fun pc =>
    match prog[pc]?, M.getD pc none with
    | some (RInstr.call t), some m => if (w t).isSome then some m.sp else none
    | _, _ => none

/-- At no destination, `callSpsT` is empty. -/
theorem callSpsT_none (prog : List RInstr) (M : Array (Option MA)) :
    callSpsT (fun _ => none) prog M = [] := by
  simp only [callSpsT, List.filterMap_eq_nil_iff]
  intro pc _
  split <;> simp

end RegionSep

namespace AbiLayout

open RegionSep

/-- The trimmed certificate of the gate at a map of destinations on `prog`: frame words are
    kept when they lie in the frame range at the stack offsets of the stores through a
    base other than `%rsp` and of the calls with a destination. -/
def ctCertRXT (σ : AbiLayout) (clob : String → Bool) (G : Nat)
    (w : Nat → Option (String × Nat)) (prog : List RInstr) : List (Option PubA) :=
  trimCertL σ (storeSps prog (inferMX σ clob G prog) ++ callSpsT w prog (inferMX σ clob G prog))
    (inferX clob G prog σ.pubAS)

/-- The frame words of the trimmed certificate at a map of destinations. -/
def ctFrameRXT (σ : AbiLayout) (clob : String → Bool) (G : Nat)
    (w : Nat → Option (String × Nat)) (prog : List RInstr) : List Int :=
  (certCells (σ.ctCertRXT clob G w prog)).eraseDups

/-- **The constant-time decision with calls of linked callees.** The map `ext` assigns each
    external entry its public argument registers and `w` its destination. The trimmed
    certificate `ctCertRXT` assigns the entry a set below `σ.pubAS`, the caller passes
    `checkCertX` at `ext`, with the registers outside `clob` and the frame words outside the
    `G`-byte footprint kept across a call, and the region check `memCheckXT` passes for the
    frame words. -/
def ctCheckRXT (σ : AbiLayout) (clob : String → Bool) (ext : Nat → Option (List String))
    (G : Nat) (w : Nat → Option (String × Nat)) (prog : List RInstr) : Bool :=
  succOk (σ.ctCertRXT clob G w prog) 0 σ.pubAS
    && checkCertX ctRegime (σ.ctFrameRXT clob G w prog) ext
      (keptRegsX clob (σ.ctCertRXT clob G w prog)) (keptCellsX G (σ.ctCertRXT clob G w prog))
      prog (σ.ctCertRXT clob G w prog)
    && memCheckXT σ clob G w (σ.ctFrameRXT clob G w prog) prog (inferMX σ clob G prog)

/-- The trimmed certificate of the gate at no destination. -/
abbrev ctCertRX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    List (Option PubA) :=
  σ.ctCertRXT clob G (fun _ => none) prog

/-- The frame words of the trimmed certificate at no destination. -/
abbrev ctFrameRX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    List Int :=
  σ.ctFrameRXT clob G (fun _ => none) prog

/-- **The constant-time decision with a call of a linked callee**: `ctCheckRXT` at the one
    entry `prog.length` and no destination. -/
abbrev ctCheckRX (σ : AbiLayout) (clob : String → Bool) (pubRegs : List String) (G : Nat)
    (prog : List RInstr) : Bool :=
  σ.ctCheckRXT clob (extOne prog.length pubRegs) G (fun _ => none) prog

/-- **The constant-time decision with a call of a linked callee and an optional
    destination**: `ctCheckRXT` at the one entry `prog.length` and the constant destination
    `dst`. -/
abbrev ctCheckRXO (σ : AbiLayout) (clob : String → Bool) (pubRegs : List String) (G : Nat)
    (dst : Option (String × Nat)) (prog : List RInstr) : Bool :=
  σ.ctCheckRXT clob (extOne prog.length pubRegs) G (fun _ => dst) prog

/-- The unfolding lemma of `ctCheckRXO` at no destination. -/
theorem ctCheckRXO_none (σ : AbiLayout) (clob : String → Bool) (pubRegs : List String)
    (G : Nat) (p : List RInstr) :
    σ.ctCheckRXO clob pubRegs G none p = σ.ctCheckRX clob pubRegs G p := rfl

/-- **Soundness of `ctCheckRXT`.** Let the region `B` hold at index `k f` the block `q f`
    without `call`, for each symbol `f` of `fs`, with distinct symbols at distinct indices.
    Let the leaky runs of `q f` meet the interface `c f`, with clobber set inside `clob`,
    footprint in the `G` bytes below the entry stack register or in the destination `w` assigns
    the target `p.length + k f`, and agreement on `callPub (pub f)` between entry states
    satisfying the precondition giving `(c f).pub`, where `ext` assigns that target the
    registers `pub f`. Let the caller `p` pass `σ.ctCheckRXT clob ext G w` and halt under the
    guarded oracles of the callees from two entry states satisfying `σ.Regions` and agreeing on
    the public data of `σ`. Then every two runs with leakage of `p ++ shiftProg p.length B`
    from these states have equal traces. -/
theorem ctCheckRXT_sound {σ : AbiLayout} {clob : String → Bool}
    {ext : Nat → Option (List String)} {G : Nat} {w : Nat → Option (String × Nat)}
    {p B : List RInstr} {fs : List String} {k : String → Nat} {q : String → List RInstr}
    {c : String → CalleeSig} {pub : String → List String}
    (h : σ.ctCheckRXT clob ext G w p = true)
    (hblock : ∀ f ∈ fs, ∃ A' B', B = A' ++ shiftProg A'.length (q f) ++ B' ∧ A'.length = k f)
    (hfree : ∀ f ∈ fs, ∀ tg, RInstr.call tg ∉ q f)
    (hinj : ∀ f ∈ fs, ∀ g ∈ fs, k f = k g → f = g)
    (hX : ∀ f ∈ fs, CalleeSpec (runOf ctRegime (q f)) (c f))
    (hclob : ∀ f ∈ fs, ∀ x, clob x = false → (c f).clob x = false)
    (hfoot : ∀ f ∈ fs, ∀ s x, (c f).foot s x → InFrame (s.regs "%rsp") G x ∨
      ∃ d ∈ w (p.length + k f), destAt d.1 d.2 s x)
    (hext : ∀ f ∈ fs, ext (p.length + k f) = some (pub f))
    (hpub : ∀ f ∈ fs, ∀ s₁ s₂, (c f).pre s₁ → (c f).pre s₂ →
      (callPub (pub f)).Agree s₁ s₂ → (c f).pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hag : σ.PubAgree s₁ s₂) (hR₁ : σ.Regions s₁)
    (hR₂ : σ.Regions s₂)
    (h₁ : HaltsO aMachine (oracleOf fs (fun f => p.length + k f)
      (fun f => guarded (c f) (runOf ctRegime (q f)))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleOf fs (fun f => p.length + k f)
      (fun f => guarded (c f) (runOf ctRegime (q f)))) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL ctRegime ok₁ (p ++ shiftProg p.length B) 0 s₁ t₁ e₁)
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length B) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  simp only [ctCheckRXT, Bool.and_eq_true] at h
  obtain ⟨⟨h0, hc⟩, hm⟩ := h
  set F := σ.ctFrameRXT clob G w p with hFdef
  set A := σ.ctCertRXT clob G w p with hAdef
  let E : String → AState → Prop := fun f => OutClearT w F (p.length + k f)
  let Y : String → CalleeRun := fun f => runOf ctRegime (q f)
  let T : Nat → CalleeRun := tracedOf fs (fun f => p.length + k f) (fun f => guarded (c f) (Y f))
  let T' : Nat → CalleeRun := tracedOf fs (fun f => p.length + k f)
    (fun f => guarded ((c f).restrictEntry (E f)) (Y f))
  have hO : ∀ tg sc0 tc sc, T tg sc0 tc sc → CallPresT clob G w tg sc0 sc := by
    rintro _ _ _ _ ⟨f, hf, rfl, hg⟩
    unfold CallPresT
    cases hw : w (p.length + k f) with
    | none =>
      exact callPres_of_guarded (hX f hf) (hclob f hf)
        (fun s x hx => (hfoot f hf s x hx).resolve_right (by simp [hw])) hg
    | some d =>
      refine callPresO_of_guarded (hX f hf) (hclob f hf) (fun s x hx => ?_) hg
      rcases hfoot f hf s x hx with hl | ⟨d', hd', hdx⟩
      · exact .inl hl
      · rw [hw, Option.mem_def, Option.some.injEq] at hd'
        subst hd'
        exact .inr hdx
  have hdown : ∀ tg s tr sc, T' tg s tr sc → T tg s tr sc :=
    fun _ _ _ _ ⟨f, hf, ht, hp, hx⟩ => ⟨f, hf, ht, hp.1, hx⟩
  have hup : ∀ tg s tr sc, (T tg s tr sc ∧ OutClearT w F tg s) → T' tg s tr sc := by
    rintro _ _ _ _ ⟨⟨f, hf, rfl, hp, hx⟩, he⟩
    exact ⟨f, hf, rfl, ⟨hp, he⟩, hx⟩
  have hsep : ∀ {s0 : AState} {t : List CTLeak} {s' : AState}, σ.Regions s0 →
      OracleRun ctRegime (fun _ _ => True) T' p 0 s0 t s' →
      OracleRun ctRegime (FrameSep F) T' p 0 s0 t s' :=
    fun hR ho => (memCheckXT_sound hm hR hO (ho.mono_oracle hdown)).mono_oracle hup
  have hH : ∀ {s0 s' : AState}, σ.Regions s0 →
      HaltsO aMachine (oracleOf fs (fun f => p.length + k f) (fun f => guarded (c f) (Y f)))
        p 0 s0 s' →
      HaltsO aMachine (oracleOf fs (fun f => p.length + k f)
        (fun f => guarded ((c f).restrictEntry (E f)) (Y f))) p 0 s0 s' := by
    intro s0 s' hR hh
    obtain ⟨t, ho⟩ := oracleRun_of_haltsO_oracleOf ctRegime hh
    exact ((memCheckXT_sound hm hR hO ho).mono_oracle hup).haltsO.mono
      fun _ _ _ ⟨tr, f, hf, ht, hx⟩ => ⟨f, hf, ht, tr, hx⟩
  have hR : ∀ f ∈ fs, ∀ x ∈ keptRegsX clob A, ((c f).restrictEntry (E f)).clob x = false := by
    intro f hf x hx
    simp only [keptRegsX, List.mem_filter, Bool.not_eq_true'] at hx
    exact hclob f hf x hx.2
  have hQ : ∀ q ∈ keptCellsX G A, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64 := by
    intro q hq
    simp only [keptCellsX, qOk, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  have hQF : ∀ q ∈ keptCellsX G A, q ∈ F.map (· + 8) := by
    intro q hq
    simp only [keptCellsX, List.mem_filter, List.mem_map] at hq
    obtain ⟨⟨a, ha, rfl⟩, _⟩ := hq
    exact List.mem_map.mpr ⟨a, by rw [hFdef, ctFrameRXT, List.mem_eraseDups]; exact ha, rfl⟩
  have hQO : ∀ f ∈ fs, ∀ s, ∀ q ∈ keptCellsX G A, ∀ x,
      InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x →
      ¬ ((∃ d ∈ w (p.length + k f), destAt d.1 d.2 s x) ∧ E f s) := by
    rintro f _ s q hq x hx ⟨⟨d, hd, hdx⟩, he⟩
    rw [Option.mem_def] at hd
    simp only [E, OutClearT, hd] at he
    exact he q (hQF q hq) x hx hdx
  obtain ⟨b, hb, hle⟩ := succOk_spec h0
  exact linkedRunX_trace_eq_blocks (ext := ext)
    (O := fun f s x => (∃ d ∈ w (p.length + k f), destAt d.1 d.2 s x) ∧ E f s) (pub := pub)
    hblock hfree hinj (fun f hf => (hX f hf).restrictEntry (E f)) hc hR
    (fun f hf s x hx => (hfoot f hf s x hx.1).imp id fun hd => ⟨hd, hx.2⟩) hQ hQO hext
    (fun f hf s₁ s₂ h₁ h₂ hp => hpub f hf s₁ s₂ h₁.1 h₂.1 hp)
    ⟨b, hb, PubA.agree_of_le hle (pubAS_agree hag hR₁ hR₂)⟩ (hH hR₁ h₁) (hH hR₂ h₂)
    (fun _ _ ho => hsep hR₁ ho) (fun _ _ ho => hsep hR₂ ho) hr₁ hr₂

/-- **Soundness of `ctCheckRXT` at one callee and a constant destination**: `ctCheckRXT_sound`
    at the one-block region `q` with its entry at the end of `p`. -/
theorem ctCheckRXT_sound_one {σ : AbiLayout} {clob : String → Bool} {pubRegs : List String}
    {G : Nat} {dst : Option (String × Nat)} {p q : List RInstr}
    (h : σ.ctCheckRXT clob (extOne p.length pubRegs) G (fun _ => dst) p = true)
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf ctRegime q) c)
    (hclob : ∀ x, clob x = false → c.clob x = false)
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x ∨ ∃ d ∈ dst, destAt d.1 d.2 s x)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hag : σ.PubAgree s₁ s₂) (hR₁ : σ.Regions s₁)
    (hR₂ : σ.Regions s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL ctRegime ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  have hO : ∀ t s s', oracleAt p.length (guarded c (runOf ctRegime q)) t s s' →
      oracleOf [""] (fun _ => p.length + 0) (fun _ => guarded c (runOf ctRegime q)) t s s' :=
    fun t s s' ho => (oracleOf_one "" p.length _ t s s').2 ho
  exact ctCheckRXT_sound (fs := [""]) (k := fun _ => 0) (q := fun _ => q) (c := fun _ => c)
    (pub := fun _ => pubRegs) h (fun _ _ => ⟨[], [], by simp [shiftProg_zero], rfl⟩)
    (fun _ _ => hq) (fun _ hf _ hg _ => by simp_all) (fun _ _ => hX) (fun _ _ => hclob)
    (fun _ _ => hfoot) (fun _ _ => by simp [extOne]) (fun _ _ => hpub) hag hR₁ hR₂
    (h₁.mono hO) (h₂.mono hO) hr₁ hr₂

/-- **Soundness of `ctCheckRX`.** Let `q` be a block without `call` whose leaky runs meet
    the interface `c`, with clobber set inside `clob`, footprint in the `G` bytes below
    the entry stack register, and agreement on `callPub pubRegs` between entry states
    satisfying the precondition giving `c.pub`. Let the caller `p` pass
    `σ.ctCheckRX clob pubRegs G` and halt under the guarded oracle of `q` from two entry
    states satisfying `σ.Regions` and agreeing on the public data of `σ`. Then every two
    runs with leakage of `p ++ shiftProg p.length q` from these states have equal
    traces. -/
theorem ctCheckRX_sound {σ : AbiLayout} {clob : String → Bool} {pubRegs : List String}
    {G : Nat} {p q : List RInstr} (h : σ.ctCheckRX clob pubRegs G p = true)
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf ctRegime q) c)
    (hclob : ∀ x, clob x = false → c.clob x = false)
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hag : σ.PubAgree s₁ s₂) (hR₁ : σ.Regions s₁)
    (hR₂ : σ.Regions s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL ctRegime ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ :=
  ctCheckRXT_sound_one (dst := none) h hq hX hclob (fun s x hf => .inl (hfoot s x hf)) hpub
    hag hR₁ hR₂ h₁ h₂ hr₁ hr₂

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
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ :=
  ctCheckRXT_sound_one (dst := some w) h hq hX hclob
    (fun s x hf => (hfoot s x hf).imp id fun hd => ⟨w, rfl, hd⟩) hpub hag hR₁ hR₂ h₁ h₂ hr₁ hr₂

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc
