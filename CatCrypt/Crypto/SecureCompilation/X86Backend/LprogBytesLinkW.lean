/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

/-!
# The byte simulation of a relocated body with carry chains and remote calls

This module simulates the address machine on the decoded program of a relocated body whose
instructions are remote transfers or lie in the wide class `DecodePrintedAddrW.instrOKWB` of carry
chains, casts, cells and one-bit names, at the correspondence `DecodePrintedAddrW.ACorrW`. The
decoded program is `LprogBytesLinkReloc.LinkedProgMap`: a multi-callee calling body reaches its
linked callee blocks through the target map `K`.

A step of the address machine at a position of such a body is `DecodePrintedAddrW.step_simWN`,
whose hypothesis on the program is the field `LinkedProgMap.blk`, and whose frame is transported
to the frame of the image by `ImageAddrFrame.stepA_congr` and `carryReq_congr`. The closing return
and the calls read the program only (`LprogBytesLinkReloc.linked_halt`, `linked_callL`), so they
keep their forms at `ACorr`.

## Main definitions

* `CallFactsW`: the facts of a printed body of the wide class with remote transfers.

## Main results

* `blkOK_of_instrOKWB`: an instruction of the wide class has the shape `blkOK`, so the decoded
  block of each covered position lies in a program that satisfies `LinkedProgMap`.
* `carryReq_congr`: the carry requirement reads the frame at the names of the body only.
* `linked_callW`: a call of such a body holds its target on the decoded program.
* `linked_stepW`: one step of the address machine is a path on the decoded program, from
  states related by `ACorrW` to states related by `ACorrW`, with the zero and carry conditions.
* `linked_segW`: the wide byte simulation of the segments of a calling body under every oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (DShape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI stepA_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## The facts of a body of the wide class -/

/-- The facts of a printed body of the wide class with remote transfers that the byte simulation
    reads: the facts `DecodePrintedAddrW.BodyFactsCW` (shapes, closing return, each other
    instruction a remote transfer or in `instrOKWB`, the compare before a conditional branch, the
    add before a carry-out binding, the widths of a cast). -/
abbrev CallFactsW (body : Lcmd) (ds : List DShape) : Prop := BodyFactsCW body ds

/-- The facts of a body of the wide class give the facts its decoded program map reads. -/
theorem CallFactsW.toLinkFacts {body : Lcmd} {ds : List DShape} (hF : CallFactsW body ds) :
    LinkFacts body ds :=
  ⟨hF.shapes, hF.pos, hF.last⟩

/-- An instruction of the wide class has the shape `blkOK`. -/
theorem blkOK_of_instrOKWB {body : Lcmd} {P : Params} {i : LinstrR}
    (h : instrOKWB body P i = true) : blkOK body i := by
  cases i with
  | Lopn ds o ss => trivial
  | Llabel kd l => trivial
  | Lcond c l =>
    cases c with
    | reg cc =>
      simp only [instrOKWB, Bool.and_eq_true] at h
      exact h.2
    | _ => simp [instrOKWB] at h
  | _ => simp [instrOKWB] at h

/-! ## The frame of the carry requirement -/

/-- One direction of `carryReq_congr`. -/
theorem carryReq_of_agree {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) {k : Nat} {sa : AState} {s : LstateA}
    (hc : CarryReq frame body k sa s) : CarryReq frame' body k sa s := by
  intro ii O A S C hb
  have hmem : ∀ q ∈ instrNames (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]),
      frame q = frame' q := fun q hq =>
    h q (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hb, hq⟩)
  have hA := hmem A (by simp [instrNames, VIR.JasminLsemExportRewrites.opNames])
  have hS := hmem S (by simp [instrNames, VIR.JasminLsemExportRewrites.opNames])
  have hC := hmem C (by simp [instrNames, VIR.JasminLsemExportRewrites.opNames])
  have := hc ii O A S C hb
  simpa only [CarryAt, wordA, bitA, hA, hS, hC] using this

/-- The carry requirement reads the frame at the names of the body only. -/
theorem carryReq_congr {frame frame' : String → Option (BitVec 64)} {body : Lcmd}
    (h : ∀ q ∈ bodyNamesI body, frame q = frame' q) (k : Nat) (sa : AState) (s : LstateA) :
    CarryReq frame body k sa s ↔ CarryReq frame' body k sa s :=
  ⟨carryReq_of_agree h, carryReq_of_agree fun q hq => (h q hq).symm⟩

/-! ## The byte simulation -/

/-- **A call of a relocated body of the wide class, on the decoded program**: the index of a call
    to the symbol `t.1` holds `call (K t.1)`, and the index of the next position is the next
    index. -/
theorem linked_callW {body : Lcmd} {ds : List DShape} (hF : CallFactsW body ds)
    {K : String → Nat} {prog : List RInstr}
    (hL : LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (p : Nat) (bi : Linstr) (ra : Option String) (t : String × LLabel)
    (hb : body[p]? = some bi) (hbi : bi.li_i = .Lcall ra t) :
    prog[posOf ds p]? = some (.call (K t.1)) ∧ posOf ds (p + 1) = posOf ds p + 1 := by
  obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
  have hkn : p + 1 < body.length := by
    by_contra hn
    have e : p = body.length - 1 := by omega
    have h1 := hF.last
    rw [(List.getElem?_eq_some_iff.mp (e ▸ hb)).2, hbi] at h1
    cases h1
  refine linked_callL hF.toLinkFacts hL p bi ra t hb hbi ?_
  rcases hF.instr p hkn with h | h
  · rwa [hbk] at h
  · rw [hbk, hbi] at h
    simp [instrOKWB] at h

/-- **One step of the address machine on a relocated body of the wide class, on the decoded
    program.** Let the body have the facts `CallFactsW`, `prog` satisfy `LinkedProgMap`, and
    `frame` agree with the frame of the body parameters at the names of the body. A step of the
    address machine, from an address state with the safety `SafeWN` that corresponds by `ACorrW`
    to a byte state `sA` with the zero flag of a conditional branch and the carry flag of a
    carry-out binding, reaches an address state at a position of the body that corresponds to a
    byte state `sA'` with the same two conditions, and the machine has a path on `prog` from the
    index of the start on `sA` to the index of the reached position on `sA'`. -/
theorem linked_stepW {body : Lcmd} {ds : List DShape} (hF : CallFactsW body ds)
    {K : String → Nat} {prog : List RInstr}
    (hL : LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (sa : LstateA) (zf : Bool) (sa' : LstateA) (zf' : Bool) (sA : AState)
    (hsafe : SafeWN rsp body sa)
    (hst : stepA frame body sa zf = some (sa', zf'))
    (hc : ACorrW rsp sA sa)
    (hz : ∀ bi, body[sa.reg.lpc]? = some bi → isCondB bi.li_i = true →
      sA.flags.zf.getD false = zf)
    (hcy : CarryReq frame body sa.reg.lpc sA sa) :
    ∃ sA', ACorrW rsp sA' sa' ∧ sa'.reg.lpc < body.length
      ∧ (∀ bi, body[sa'.reg.lpc]? = some bi → isCondB bi.li_i = true →
          sA'.flags.zf.getD false = zf')
      ∧ CarryReq frame body sa'.reg.lpc sA' sa'
      ∧ Reaches aMachine prog (posOf ds sa.reg.lpc) sA (posOf ds sa'.reg.lpc) sA' := by
  rw [stepA_congr hfr] at hst
  rw [carryReq_congr hfr] at hcy
  cases hb : body[sa.reg.lpc]? with
  | none => simp [stepA, hb] at hst
  | some bi =>
    obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
    have hkn : sa.reg.lpc + 1 < body.length := by
      by_contra hn
      have e : sa.reg.lpc = body.length - 1 := by omega
      have h1 := hF.last
      rw [(List.getElem?_eq_some_iff.mp (e ▸ hb)).2] at h1
      obtain ⟨ii, li⟩ := bi
      simp only at h1
      subst h1
      simp [stepA, hb] at hst
    have hblk : blkOK body bi.li_i := by
      rcases hF.instr sa.reg.lpc hkn with h | h
      · rw [hbk] at h
        obtain ⟨ii, li⟩ := bi
        cases li <;> first
          | (simp [remoteSym] at h; done)
          | simp [stepA, hb] at hst
      · rw [hbk] at h
        exact blkOK_of_instrOKWB h
    obtain ⟨sb, hR, hc', hl, hz', hcy'⟩ := step_simWN hF rsp (prog := prog) (k := sa.reg.lpc)
      (fun hs => hL.blk _ hk hs (by rw [hbk]; exact hblk)) sA sa zf sa' zf' rfl hk hkn hc
      (fun hcnd => hz _ (List.getElem?_eq_getElem hk) hcnd) hcy hsafe hst
    refine ⟨sb, hc', hl, fun bi' hb' hcnd => ?_, (carryReq_congr hfr _ _ _).mpr hcy', hR⟩
    rw [(List.getElem?_eq_some_iff.mp hb').2] at hz'
    exact hz' hcnd

/-- **The byte simulation of the segments of a relocated body of the wide class.** Let the body
    have the facts `CallFactsW`, `prog` satisfy `LinkedProgMap` at the target map `K`, and `frame`
    agree with the frame of the body parameters at the names of the body. Under every oracle `O`,
    with the index `DecodePrintedCFG.posOf` of a position:

    * a step of the address machine, from an address state with the safety `SafeWN` that
      corresponds by `ACorrW` to a byte state with the zero flag of a conditional branch and the
      carry flag of a carry-out binding, reaches an address state at a position of the body with
      the same conditions, and every run under `O` from the index of the reached position extends
      to a run from the index of the start;
    * at the closing return, from a byte state related by `ACorr`, there is a run under `O` to a
      byte state that satisfies `FinLea` with the address state;
    * the index of a call to the symbol `t.1` holds `call (K t.1)`, and the index of the position
      after a call is the index after the call. -/
theorem linked_segW {body : Lcmd} {ds : List DShape} (hF : CallFactsW body ds)
    {K : String → Nat} {prog : List RInstr}
    (hL : LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (O : Nat → AState → AState → Prop) :
    (∀ sa zf sa' zf' sA, SafeWN rsp body sa →
        stepA frame body sa zf = some (sa', zf') → ACorrW rsp sA sa →
        (∀ bi, body[sa.reg.lpc]? = some bi → isCondB bi.li_i = true →
          sA.flags.zf.getD false = zf) →
        CarryReq frame body sa.reg.lpc sA sa →
        ∃ sA', ACorrW rsp sA' sa' ∧ sa'.reg.lpc < body.length
          ∧ (∀ bi, body[sa'.reg.lpc]? = some bi → isCondB bi.li_i = true →
              sA'.flags.zf.getD false = zf')
          ∧ CarryReq frame body sa'.reg.lpc sA' sa'
          ∧ ∀ s'', HaltsO aMachine O prog (posOf ds sa'.reg.lpc) sA' s'' →
              HaltsO aMachine O prog (posOf ds sa.reg.lpc) sA s'')
      ∧ (∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
          ∃ sA', HaltsO aMachine O prog (posOf ds sa.reg.lpc) sA sA'
            ∧ FinLea rsp (Params.ofBody body).frame sa sA')
      ∧ (∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
          prog[posOf ds p]? = some (.call (K t.1)))
      ∧ (∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
          posOf ds (p + 1) = posOf ds p + 1) := by
  refine ⟨fun sa zf sa' zf' sA hsafe hst hc hz hcy => ?_, fun sa sA hend hc => ?_,
    fun p bi ra t hb hbi => (linked_callW hF hL p bi ra t hb hbi).1,
    fun p bi ra t hb hbi => (linked_callW hF hL p bi ra t hb hbi).2⟩
  · obtain ⟨sA', hc', hlen, hz', hcy', hR⟩ :=
      linked_stepW hF hL rsp hfr sa zf sa' zf' sA hsafe hst hc hz hcy
    exact ⟨sA', hc', hlen, hz', hcy', fun s'' hr => haltsO_of_reaches hR hr⟩
  · exact ⟨_, linked_halt hL O sa sA hend, sA, hc, rfl⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW
