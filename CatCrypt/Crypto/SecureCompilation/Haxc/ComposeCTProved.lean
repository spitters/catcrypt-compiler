/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageRouteCT
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCT
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTPub
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the bytes of the single-loop image route from the proved chain

This module derives the constant-time conjunct on the looped image route from the level check of the front: `nfFront_routeCT_opt` gives constant
time of the route program, `virtB_memFCT` of the virtual body, `memFCT_of_ownedCheckML` of
the image of the printed body, and the image simulation with its events gives constant time
of the decoded bytes.

The statements `image_addr_ct`, `image_bytes_ct` and `route_bytes_ct` assume a printed body
without a conditional branch (`NoCond`). The printed body of a loop has the branches of its
guard and of its back edge, so sections 1 to 5 state and prove them for bodies with
conditional branches. The trace of the address machine is related to the trace of the image
by `PhysTr`, which follows the program counter through the branch events.

The hypotheses of `v1Loop_bytes_ct` on a looped program and a printed body:

* the image gate `v1LoopB` and its check on traced runs `v1LoopLB` (`BackHalf`): the checker
  `ownedCheckML` accepts the pair that the image gate compares with `ownedCheckMC`;
* constant time of the source events for labels `L`;
* `PubLabelsOK`: the labels mark public only scalar parameters that the layout bounds, so
  agreement on the public data of the layout gives agreement of the valuations on the public
  labels (`pubLabelsB` is its check on a secrecy record);
* every entry state has a valuation, which holds when the names of the layout are pairwise
  distinct (`exists_abiValOf`).

The statements for `compileA` are in `ComposeCTStraight`.

## Main definitions

* `ImageLoopCT.nxtA`, `ImageLoopCT.PhysTr` — the program counter after an instruction of a
  printed body, read off the events of its image, and the relation between the trace of the
  image and the trace of the address machine along the run.
* `PubLabelsOK`, `pubLabelsB` — agreement of labels with the public data of a layout, and
  its check on a secrecy record.

## Main results

* `ImageLoopCT.image_addr_trace` — every halting checked run of the image of a gated printed
  body, with or without conditional branches, is matched by a halting traced run of the
  address machine whose trace is related to the trace of the image by `PhysTr`.
* `ImageLoopCT.image_addr_ct_cfg`, `ImageLoopCT.image_bytes_ct_cfg`,
  `ImageLoopCT.route_bytes_ct_loop` — the statements of `image_addr_ct`, `image_bytes_ct`
  and `route_bytes_ct` for printed bodies with conditional branches.
* `v1Loop_bytes_ct` — constant time of the bytes of a looped program that passes the image
  gate, between entry states that satisfy `σ.Regions` and agree on the public data of `σ`.
* `pubLabelsOK_of_pubLabelsB`, `exists_abiValOf` — the label condition from its check, and a
  valuation of every entry state.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (fstepA_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (labelAt_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next
  NextPc)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-! ## 1. The program counter after a step -/

/-- A step of the address machine at an instruction other than a conditional branch
    advances the program counter by one. -/
theorem stepA_lpc_notCond {frame : String → Option (BitVec 64)} {body : Lcmd}
    {sa sa1 : LstateA} {zf z1 : Bool} {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    (hnc : ∀ c l, bi.li_i ≠ .Lcond c l)
    (h : stepA frame body sa zf = some (sa1, z1)) : sa1.reg.lpc = sa.reg.lpc + 1 := by
  unfold stepA at h
  split at h
  · exact fstepA_lpc frame _ sa sa1 zf z1 h
  · cases h
    rfl
  · rename_i ii cc l hbi
    rw [hb] at hbi
    cases hbi
    exact absurd rfl (hnc (.reg cc) l)
  · cases h

/-- A step of the address machine changes the program counter. -/
theorem stepA_lpc_ne {frame : String → Option (BitVec 64)} {body : Lcmd}
    {sa sa1 : LstateA} {zf z1 : Bool}
    (h : stepA frame body sa zf = some (sa1, z1)) : sa1.reg.lpc ≠ sa.reg.lpc := by
  unfold stepA at h
  split at h
  · have := fstepA_lpc frame _ sa sa1 zf z1 h
    omega
  · cases h
    simp [LstateA.setLpc]
  · rename_i ii cc l hbi
    split at h
    · split at h
      · obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp h
        cases hpe
        obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
        intro heq
        simp only [LstateA.setLpc] at heq
        subst heq
        have hbe : body[sa.reg.lpc] = ⟨ii, .Lcond (.reg cc) l⟩ :=
          Option.some.inj ((List.getElem?_eq_getElem hpl).symm.trans hbi)
        rw [hbe] at hlab
        simp [isLabelB] at hlab
      · cases h
        simp [LstateA.setLpc]
    · cases h
  · cases h

/-- **The program counter after instruction `x` at position `k`** of a printed body, from
    the events `e` of its image: one past the label of a conditional branch whose event is
    the taken decision, `k + 1` otherwise. -/
def nxtA (body : Lcmd) (k : Nat) (x : LinstrR) (e : List CTLeak) : Nat :=
  match x, e with
  | .Lcond _ l, [.branch true] => (labelAt body l).getD 0 + 1
  | _, _ => k + 1

theorem nxtA_notCond (body : Lcmd) (k : Nat) {x : LinstrR} (h : ∀ c l, x ≠ .Lcond c l)
    (e : List CTLeak) : nxtA body k x e = k + 1 := by
  unfold nxtA
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- **The trace of the address machine along a run of the image.** From position `k` of the
    body, the trace `ℓ` of the image is cut into the events of each instruction on the path
    the events select (`nxtA`), and the trace of the address machine is `posT` of each
    piece. -/
inductive PhysTr (frame : String → Option (BitVec 64)) (base : String → BitVec 64)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    Nat → List CTLeak → List CTLeak → Prop
  | halt (k : Nat) (h : body.dropLast[k]? = none) : PhysTr frame base slotArr body k [] []
  | step (k : Nat) (x : Linstr) (e ℓ ℓA : List CTLeak) (hx : body.dropLast[k]? = some x)
      (he : e.length = evCountF (imgInstr slotArr body k x.li_i))
      (h : PhysTr frame base slotArr body (nxtA body k x.li_i e) ℓ ℓA) :
      PhysTr frame base slotArr body k (e ++ ℓ)
        (posT frame base x.li_i (imgInstr slotArr body k x.li_i) e ++ ℓA)

/-- The trace of the address machine is a function of the start position and the trace of
    the image. -/
theorem PhysTr.unique {frame : String → Option (BitVec 64)} {base : String → BitVec 64}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {ℓ a₁ a₂ : List CTLeak}
    (h₁ : PhysTr frame base slotArr body k ℓ a₁) (h₂ : PhysTr frame base slotArr body k ℓ a₂) :
    a₁ = a₂ := by
  induction h₁ generalizing a₂ with
  | halt k h =>
      generalize hv : ([] : List CTLeak) = v at h₂
      cases h₂ with
      | halt _ _ => rfl
      | step _ x e ℓ' ℓA hx he h' => rw [h] at hx; cases hx
  | step k x e ℓ' ℓA hx he h ih =>
      generalize hv : e ++ ℓ' = v at h₂
      cases h₂ with
      | halt _ h0 => rw [h0] at hx; cases hx
      | step _ x' e' ℓ'' ℓA' hx' he' h' =>
          rw [hx] at hx'
          cases hx'
          obtain ⟨rfl, rfl⟩ := List.append_inj hv (he.trans he'.symm)
          rw [ih h']

/-! ## 2. One step of the image with its events -/

/-- **One step of the image with its events.** From related states, a checked step of the
    image of instruction `bi` of a gated body is matched by steps of the address machine to a
    related state at the program counter `nxtA` selects from the events of the image
    instruction; every traced run of the address machine from that state extends to a traced
    run from the start whose trace is prefixed by `posT` of those events. -/
theorem img_step_trace {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) {s t : LstateMF}
    (hfn : s.prog.lfn = fn) {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hlt : sa.reg.lpc < body.length - 1) (hb : body[sa.reg.lpc]? = some bi)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr body))
      (imgInstr slotArr body sa.reg.lpc bi.li_i) s = some t) :
    ∃ sa' zf', ImgRel frame slotArr base body t sa' zf'
      ∧ sa'.reg.lpc = nxtA body sa.reg.lpc bi.li_i
          (instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s)
      ∧ ∀ fuel r ℓ, runALeak frame body fuel sa' zf' = some (r, ℓ) →
          ∃ fuel', runALeak frame body fuel' sa zf = some (r,
            posT frame base bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i)
              (instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s) ++ ℓ) := by
  set P := singletonProgM fn (virtImg slotArr body) with hP
  set e := instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s with he
  have hfetch : findInstrMem P s.prog = some (imgInstr slotArr body sa.reg.lpc bi.li_i) := by
    rw [findInstrMem_single hfn, virtImg_getElem?, ← hrel.pc, List.getElem?_dropLast,
      ite_eq_left hlt, hb]
    rfl
  obtain ⟨hh, -, -, sa1, z1, hst1, hcase⟩ :=
    img_step hsep hphys hgate fn hfn hrel hfetch hstep
  have hsl : stepLeakA frame body sa zf
      = posT frame base bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i) e :=
    step_leak hsep hgate hrel hlt hb
  have hg : instrGateB frame slotArr body sa.reg.lpc bi.li_i = true := by
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  have hev := evalInstrPMemF_of_k hstep
  have one : ∀ fuel r ℓ, runALeak frame body fuel sa1 z1 = some (r, ℓ) →
      runALeak frame body (fuel + 1) sa zf
        = some (r, posT frame base bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i) e ++ ℓ) := by
    intro fuel r ℓ h
    rw [runALeak_step frame body fuel sa zf hh, hst1, Option.bind_some, h, hsl]
    rfl
  by_cases hcnd : ∃ cc l, bi.li_i = .Lcond (.reg cc) l
  · obtain ⟨cc, l, hx⟩ := hcnd
    have hc : icase frame bi.li_i = .cond cc l := by rw [hx]; rfl
    have hg' := hg
    unfold instrGateB at hg'
    rw [hc] at hg'
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hg'
    obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hg'
    have hi : imgInstr slotArr body sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
      rw [hx]; rfl
    obtain ⟨r0, hr0, hret⟩ := imgGateB_last hgate
    have hfl := findLabel_virtImg slotArr body l (fun r' hr' => by
      rw [hr0] at hr'
      cases hr'
      rw [hret]; rfl)
    rw [hp] at hfl
    have hz : s.zf = zf := hrel.zf
    have hstep' := hstep
    rw [hi, evalInstrPMemFk_reg, hx, eval_cond fn _ cc l _ hpol hfl] at hstep'
    have hstepA : stepA frame body sa zf = if zf = pol then some (sa.setLpc p, zf)
        else some (sa.setLpc (sa.reg.lpc + 1), zf) := by
      obtain ⟨ii0, li⟩ := bi
      simp only at hx
      subst hx
      simp only [stepA, hb, hpol, hp, Option.map_some]
    have hslA : stepLeakA frame body sa zf = [.branch (zf == pol)] := by
      obtain ⟨ii0, li⟩ := bi
      simp only at hx
      subst hx
      simp only [stepLeakA, hb, hpol]
    have hpe : posT frame base bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i) e = e := by
      simp only [posT, hc]
    have hee : e = [.branch (zf == pol)] := by rw [← hpe, ← hsl, hslA]
    by_cases hzp : zf = pol
    · rw [ite_eq_left (hz.trans hzp)] at hstep'
      have ht : t.prog.base.reg.lpc = p + 1 := by
        cases hstep'
        rfl
      rw [ite_eq_left hzp] at hstepA
      rw [hstepA] at hst1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst1)
      obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
      have hbp : body[p]? = some body[p] := List.getElem?_eq_getElem hpl
      obtain ⟨ii', hli⟩ : ∃ ii', body[p].li_i = .Llabel ii' l := by
        revert hlab
        cases body[p].li_i <;> simp [isLabelB]
      have hst2 : stepA frame body (sa.setLpc p) zf = some (sa.setLpc (p + 1), zf) := by
        generalize body[p] = bp at hli hbp
        obtain ⟨ii1, li1⟩ := bp
        simp only at hli
        subst hli
        simp [stepA, LstateA.setLpc, hbp]
      have hsl2 : stepLeakA frame body (sa.setLpc p) zf = [] := by
        generalize body[p] = bp at hli hbp
        obtain ⟨ii1, li1⟩ := bp
        simp only at hli
        subst hli
        simp [stepLeakA, LstateA.setLpc, hbp]
      rcases hcase with hrel1 | ⟨hh1, -, sa2, z2, hs2, hrel2⟩
      · have h1 := hrel1.pc
        simp only [LstateA.setLpc] at h1
        omega
      · rw [hst2] at hs2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs2)
        refine ⟨_, _, hrel2, ?_, ?_⟩
        · rw [hee, hx]
          simp [nxtA, hp, hzp, LstateA.setLpc]
        · intro fuel r ℓ h
          refine ⟨fuel + 2, one (fuel + 1) r ℓ ?_⟩
          rw [runALeak_step _ _ _ _ _ hh1, hst2, Option.bind_some, h, hsl2]
          rfl
    · rw [ite_eq_right (fun h => hzp (hz.symm.trans h))] at hstep'
      have ht : t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
        cases hstep'
        rfl
      rw [ite_eq_right hzp] at hstepA
      rw [hstepA] at hst1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst1)
      rcases hcase with hrel1 | ⟨-, -, sa2, z2, hs2, hrel2⟩
      · refine ⟨_, _, hrel1, ?_, fun fuel r ℓ h => ⟨_, one fuel r ℓ h⟩⟩
        rw [hee, hx]
        simp [nxtA, hzp, LstateA.setLpc]
      · exfalso
        have h1 := stepA_lpc_ne hs2
        have h2 := hrel2.pc
        have h0 := hrel.pc
        simp only [LstateA.setLpc] at h1
        omega
  · have hncb : ∀ c l, bi.li_i ≠ .Lcond c l := by
      intro c l hx
      cases c with
      | reg cc => exact hcnd ⟨cc, l, hx⟩
      | _ =>
          have hg' := hg
          unfold instrGateB at hg'
          rw [hx] at hg'
          simp [icase] at hg'
    have hpc1 := stepA_lpc_notCond hb hncb hst1
    have hvpc : t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 :=
      imgInstr_nextPc hg hncb _ _ _ (evalInstrPMemF_next P _ s t hev).2
    rcases hcase with hrel1 | ⟨-, -, sa2, z2, hs2, hrel2⟩
    · exact ⟨sa1, z1, hrel1, by rw [nxtA_notCond body _ hncb, hpc1],
        fun fuel r ℓ h => ⟨_, one fuel r ℓ h⟩⟩
    · exfalso
      have h1 := stepA_lpc_ne hs2
      have h2 := hrel2.pc
      have h0 := hrel.pc
      omega

/-! ## 3. Runs -/

/-- **The traced image simulation.** For a printed body that passes the gate `imgGateB` and
    the class `physImgB`, at a separation `ImgSep`, every halting checked run of the image
    from a state related to an address state has a traced run with a trace `ℓ`, and is
    matched by a halting traced run of the address machine on the body whose trace is
    related to `ℓ` by `PhysTr` from the program counter of the start. -/
theorem image_addr_trace {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel s = some t →
      ∃ ℓ ℓA fuel' r,
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr body)) fuel s = some (t, ℓ)
        ∧ runALeak frame body fuel' sa zf = some (r, ℓA)
        ∧ PhysTr frame base slotArr body sa.reg.lpc ℓ ℓA := by
  set P := singletonProgM fn (virtImg slotArr body)
  have halt : ∀ (s : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf → findInstrMem P s.prog = none →
      ∀ fuel, ∃ ℓ ℓA fuel' r,
        lsemFuelMemFLeak P fuel s = some (s, ℓ)
        ∧ runALeak frame body fuel' sa zf = some (r, ℓA)
        ∧ PhysTr frame base slotArr body sa.reg.lpc ℓ ℓA := by
    intro s sa zf hfn hrel hf fuel
    have hnone : body.dropLast[sa.reg.lpc]? = none := by
      have h := hf
      rw [findInstrMem_single hfn, List.getElem?_eq_none_iff, virtImg_length, ← hrel.pc] at h
      rw [List.getElem?_eq_none_iff, List.length_dropLast]
      exact h
    exact ⟨[], [], 0, (sa, zf), lsemFuelMemFLeak_halt P fuel s hf,
      runALeak_halt frame body 0 sa zf (haltedA_of_img (.of_imgGateB hgate) fn hfn hrel.pc hf),
      .halt _ hnone⟩
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf 0
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf (f + 1)
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true P i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              have hfetch := hf
              rw [findInstrMem_single hfn, virtImg_getElem?, ← hrel.pc,
                List.getElem?_dropLast] at hfetch
              split at hfetch
              case isFalse => cases hfetch
              rename_i hlt
              obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hfetch
              obtain ⟨sa', zf', hrel', hpc', hcomp⟩ :=
                img_step_trace hsep hphys hgate fn hfn hrel hlt hb he
              have hev := evalInstrPMemF_of_k he
              have hfn1 : s1.prog.lfn = fn :=
                (evalInstrPMemF_next P _ s s1 hev).1.trans hfn
              obtain ⟨ℓ', ℓA', f', r, hl', hr', hT⟩ := ih s1 t sa' zf' hfn1 hrel' hrun
              obtain ⟨f'', hr''⟩ := hcomp f' r ℓA' hr'
              refine ⟨instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s ++ ℓ', _, f'', r,
                ?_, hr'', ?_⟩
              · rw [lsemFuelMemFLeak_step P f _ s s1 hf hev, hl']
                rfl
              · refine .step _ bi _ _ _ ?_ (instrLeakF_length _ _) (hpc' ▸ hT)
                rw [List.getElem?_dropLast, ite_eq_left hlt, hb]

/-! ## 4. Constant time -/

/-- **Constant time of the address machine from constant time of the image**, for a printed
    body with or without conditional branches that passes the gate and the class, at a
    separation: constant time of the image on the flag machine gives constant time of the
    address machine on the body between public-equal address states (`AddrPub`). -/
theorem image_addr_ct_cfg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String)
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr body)) pubEq) :
    ConstantTimeRel (AddrPub frame slotArr base body fn pubEq) (ARun frame body) := by
  rintro ⟨sa₁, zf₁⟩ ⟨sa₂, zf₂⟩ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hA₁⟩ ⟨g₂, r₂, hA₂⟩
  obtain ⟨v₁, a₁, F₁, q₁, hv₁, hL₁, hT₁⟩ :=
    image_addr_trace hsep hphys hgate fn f₁ s₁ t₁ sa₁ zf₁ hfn₁ hr₁ hk₁
  obtain ⟨v₂, a₂, F₂, q₂, hv₂, hL₂, hT₂⟩ :=
    image_addr_trace hsep hphys hgate fn f₂ s₂ t₂ sa₂ zf₂ hfn₂ hr₂ hk₂
  have hv : v₁ = v₂ := hct s₁ s₂ v₁ v₂ hpub ⟨f₁, t₁, hv₁⟩ ⟨f₂, t₂, hv₂⟩
  have e₁ := congrArg Prod.snd (runALeak_det frame body g₁ F₁ sa₁ zf₁ _ _ hA₁ hL₁)
  have e₂ := congrArg Prod.snd (runALeak_det frame body g₂ F₂ sa₂ zf₂ _ _ hA₂ hL₂)
  have hsp : sa₁.reg.lpc = sa₂.reg.lpc := by rw [hr₁.pc, hr₂.pc, hpc]
  simp only at e₁ e₂
  subst hv
  rw [hsp] at hT₁
  rw [e₁, e₂]
  exact PhysTr.unique hT₁ hT₂

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (ImgBytePub
  bytes_trace_eq aRun_frameIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn runA_frameIn
  runSafe_frameIn imgGateB_frameMark)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)

/-- **Constant time of the decoded bytes from constant time of the image**, for a printed
    body in `printedAddrB`, with or without conditional branches, that passes the gates of
    the image simulation at its frame below `rsp` and is separated there: constant time of
    the image on the flag machine gives constant time of the decoded function bytes under
    the regime `doitm` and any side condition, between machine states related by
    `ImgBytePub`. -/
theorem image_bytes_ct_cfg {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd} {rsp : BitVec 64}
    (hpr : printedAddrB body = true) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB (frameIn body (frameP (Params.ofBody body) rsp)) slotArr body = true)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) rsp)) slotArr base rsp)
    (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr body)) pubEq)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (ImgBytePub rsp slotArr base body fn pubEq)
      (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  rintro sa₁ sa₂ u₁ u₂ ⟨hr₁, hr₂, a₁, a₂, hpub, he₁, he₂⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩
  have hA := image_addr_ct_cfg hsep hphys hgate fn hct
  have hpub' := hpub
  obtain ⟨s₁, s₂, -, -, hfn₁, hfn₂, hR₁, hR₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩ := hpub'
  obtain ⟨g₁, sa₁', zf₁', hrA₁, -, hs₁⟩ :=
    image_addr_sim hsep hphys hgate fn f₁ s₁ t₁ a₁.1 a₁.2 hfn₁ hR₁ hk₁
  obtain ⟨g₂, sa₂', zf₂', hrA₂, -, hs₂⟩ :=
    image_addr_sim hsep hphys hgate fn f₂ s₂ t₂ a₂.1 a₂.2 hfn₂ hR₂ hk₂
  rw [runA_frameIn] at hrA₁ hrA₂
  rw [runSafe_frameIn] at hs₁ hs₂
  exact bytes_trace_eq hpr hdec hr₁ hr₂ he₁ he₂ ⟨g₁, _, hrA₁, hs₁⟩ ⟨g₂, _, hrA₂, hs₂⟩
    (fun ℓ₁ ℓ₂ h₁ h₂ => hA a₁ a₂ ℓ₁ ℓ₂ hpub ((aRun_frameIn body _ a₁ ℓ₁).mpr h₁)
      ((aRun_frameIn body _ a₂ ℓ₂).mpr h₂)) hb₁ hb₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopCT

/-! ## 5. The image route -/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (MemFCT instrLeakB
  lsemFuelMemFLeak lsemFuelMemFLeak_fst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk
  lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop (certNode loopCertB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (routeB virtB slotRen
  slotArrOf entryB_spec boundFacts_entryV routeB_abiEntry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (RouteEntryPub virtB_memFCT
  routeEntry virtB_leak certNode_noCArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels PubEqV)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn imgGateB_frameMark)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (ImgBytePub)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf
  singleLoop_export_faithful_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)

/-- **Constant time of the decoded bytes of the image route from the source**: the statement
    of `ImageRouteCT.route_bytes_ct` for a printed body with conditional branches. -/
theorem route_bytes_ct_loop (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String}
    (hg : routeB σ nm body seeds loop ps fuse outR = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = []) (L : Labels Γ)
    (fn : String)
    (hct : CT.ConstantTime (PubEqV L)
      (ComL.ctLeak (jLeakModel Pj) (singleLoop update count init invs)))
    (hlk : ownedCheckML [] (virtB σ nm seeds loop ps fuse)
      (virtImg (slotRen (slotArrOf σ nm) (renOf ps)) body) = true)
    {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) rsp))
      (slotRen (slotArrOf σ nm) (renOf ps)) base rsp)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel
      (ImgBytePub rsp (slotRen (slotArrOf σ nm) (renOf ps)) base body fn
        (TVPub fn (virtB σ nm seeds loop ps fuse) (RouteEntryPub σ body ps fn L)))
      (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hg' := hg
  simp only [routeB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hpr⟩, hphys⟩, hgate⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
  have hgate' : ImageAddrSim.imgGateB (frameIn body (frameP (Params.ofBody body) rsp))
      (slotRen (slotArrOf σ nm) (renOf ps)) body = true := by
    rw [imgGateB_frameMark]; exact hgate
  exact image_bytes_ct_cfg hpr hphys hgate' hsep fn
    (memFCT_of_ownedCheckML hlk fn (virtB_memFCT Pj update count init invs outArg inArgs
      abiArgs hupd hexp hcert out c hi hcn hg hnode hqs L fn hct)) ok hdec

/-- **The virtual body of the image route halts on checked runs.** Under the hypotheses of
    `route_bytes_ct_loop` on the program and the route check, from the entry state of every
    machine state that satisfies `σ.Regions` and has a valuation the layout reads off it, the
    virtual body has a halting checked run. -/
theorem virtB_checked_run {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true)
    (out c : String) (hi : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcn : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    {σ : AbiLayout} {nm : String → String} {body : Lcmd} {seeds loop : List LinstrRM}
    {ps : List (String × String)} {fuse : Bool} {outR : String}
    (hg : routeB σ nm body seeds loop ps fuse outR = true)
    (hnode : seeds ++ loop = certNode update invs out c)
    (hqs : ∀ i ∈ seeds, ∀ r, instrLeakB r i = [])
    (sa : AState) (hreg : σ.Regions sa) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V)
    (fn : String) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (virtB σ nm seeds loop ps fuse)) f
      (routeEntry σ body ps fn sa) = some t := by
  have habi := routeB_abiEntry hg sa
  obtain ⟨out', c', hi', hc', -, hrun⟩ :=
    singleLoop_export_faithful_abi update count init invs outArg inArgs abiArgs hupd hexp hcert
  rw [hi] at hi'
  cases hi'
  rw [hcn] at hc'
  cases hc'
  obtain ⟨k, t, hk, -⟩ := hrun σ sa V fn _ false hV habi
  have hfst := lsemFuelMemFLeak_fst (singletonProgM fn (certNode update invs out c)) k
    (routeEntry σ body ps fn sa)
  rw [hk] at hfst
  obtain ⟨r0, hr0, -⟩ := Option.map_eq_some_iff.mp hfst
  have ha : ∀ i ∈ loop, ImageAddrLeak.NoCArr i.1 := fun i hi0 =>
    certNode_noCArr update count init invs outArg inArgs abiArgs hexp hcert out c hi hcn i
      (hnode ▸ List.mem_append_right _ hi0)
  rw [← hnode] at hr0
  obtain ⟨f', t', ht'⟩ := virtB_leak hg hqs ha sa hreg.stackIn fn k r0.1 r0.2 hr0
  have hrun' : lsemFuelMemF (singletonProgM fn (virtB σ nm seeds loop ps fuse)) f'
      (routeEntry σ body ps fn sa) = some t' := by
    rw [← lsemFuelMemFLeak_fst, ht']
    rfl
  have hg' := hg
  simp only [routeB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hidx⟩, -⟩, -⟩, -⟩, -⟩, hent⟩, -⟩, -⟩, -⟩ := hg'
  have E := entryB_spec hent sa
  have hents := boundFacts_entryV (nm := nm) (fr := ImageAddrRoute.frameE body sa)
    (un := ImageAddrRoute.unren ps) hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ t' rfl rfl (hents _) f' hrun'
  exact ⟨f', t', lsemFuelMemFk_of_runIdxOk true _ f' _ t' hrun' hok⟩

/-- The relation of the image simulation depends on the array bases only at the arrays of
    the slot map. -/
theorem imgRel_congr_base {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base base' : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : JasminLsemAddrMem.LstateA} {zf : Bool}
    (h : ∀ q A n, slotArr q = some (A, n) → base A = base' A)
    (hr : ImgRel frame slotArr base body s sa zf) : ImgRel frame slotArr base' body s sa zf :=
  ⟨hr.pc, hr.regs, hr.slots, hr.zf, hr.cf, hr.of, hr.wid,
    fun q A n hq => by rw [← h q A n hq]; exact hr.cells q A n hq,
    fun k R A n a hs hq hf => by rw [← h _ A n hq]; exact hr.saved k R A n a hs hq hf,
    hr.reload, fun R A n a hR hq hf => by rw [← h _ A n hq]; exact hr.held R A n a hR hq hf⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopCT

/-! ## 6. The image gate of a looped program -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (guardedFlagLoopLinstrRM
  LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels PubEqV lvlOf)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf argIdx wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (arrMemNB comExpOKB
  arrMemNB_sound comExpOKB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody (loopCertNB
  loopCertB_of_loopCertNB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (singleLoop)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf synthRen
  routeB virtB slotRen entryA unren entryB_spec renB_spec imgRel_entryV entryB_save imgSep_slotRen
  slotArrOf_some slotRen_some abiBase_argName frameE)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (RouteEntryPub routeEntry
  loopSeedsRM_quiet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (imgSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageLoopCT (route_bytes_ct_loop
  virtB_checked_run imgRel_congr_base)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys gpOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (Entry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime ConstantTimeRel)

/-- **The labels agree with the public data of the layout**: every position the labels `L`
    mark public is a register variable whose parameter is public under `σ`
    (`AbiLayout.argPub`), or an array variable of `64`-bit words whose parameter is an array
    of that length with its register in `σ.pubWords`, a public array of the layout. -/
def PubLabelsOK (σ : AbiLayout) {Γ : Ctxt jasminDialect} (L : Labels Γ) : Prop :=
  ∀ (t : JasminTy) (v : Ctxt.Var Γ t), lvlOf v L = .Public →
    (∃ w a, t = .reg w ∧ σ.args[argIdx v]? = some a ∧ σ.argPub a = true) ∨
      ∃ n a, t = .stackArr 64 n ∧ σ.args[argIdx v]? = some a ∧ a.kind = .words n ∧
        a.reg ∈ σ.pubWords

/-- Equal words read by `wordsAt` give equal word functions `wordsFn`. -/
theorem wordsFn_eq_of_wordsAt_eq {sa₁ sa₂ : AState} {b₁ b₂ : BitVec 64} {n : Nat}
    (h : wordsAt sa₁.mem b₁ n = wordsAt sa₂.mem b₂ n) :
    wordsFn sa₁ b₁ n = wordsFn sa₂ b₂ n := by
  funext i
  have hi := congrArg (·[i.val]?) h
  simp only [wordsAt, List.getElem?_map, List.getElem?_range i.isLt,
    Option.map_some, Option.some.injEq, _root_.Hax.Value.int.injEq] at hi
  exact BitVec.eq_of_toNat_eq (Int.ofNat_inj.mp hi)

/-- Under `PubLabelsOK`, the valuations the layout reads off two entry states that agree on
    its public data agree on the positions the labels mark public. -/
theorem pubEqV_of_pubAgree {σ : AbiLayout} {Γ : Ctxt jasminDialect} {L : Labels Γ}
    (hL : PubLabelsOK σ L) {sa₁ sa₂ : AState} {V₁ V₂ : Ctxt.Valuation Γ}
    (hag : σ.PubAgree sa₁ sa₂) (h₁ : AbiValOf σ sa₁ V₁) (h₂ : AbiValOf σ sa₂ V₂) :
    PubEqV L V₁ V₂ := by
  intro t v hv
  rcases hL t v hv with ⟨w, a, rfl, ha, hp⟩ | ⟨n, a, rfl, ha, hk, hm⟩
  · obtain ⟨a₁, ha₁, -, hw, e₁⟩ := h₁.reg v
    obtain ⟨a₂, ha₂, -, hw', e₂⟩ := h₂.reg v
    rw [ha] at ha₁ ha₂
    cases ha₁
    cases ha₂
    subst hw
    rw [e₁, e₂]
    exact hag.regs a (List.mem_of_getElem? ha) hp
  · obtain ⟨a₁, ha₁, -, hw₁, e₁⟩ := h₁.arr v
    obtain ⟨a₂, ha₂, -, hw₂, e₂⟩ := h₂.arr v
    rw [ha] at ha₁ ha₂
    cases ha₁
    cases ha₂
    rw [e₁, e₂]
    exact wordsFn_eq_of_wordsAt_eq (hag.words a (List.mem_of_getElem? ha) n hk hm)

/-- **Constant time of the bytes of a looped program through the image route.** Let the
    looped program `c` pass the image gate `v1LoopB` and the check on traced runs `v1LoopLB`
    against the printed body `body`, let its source events be constant time for labels `L`
    that agree with the public data of `σ`, and let every entry state satisfying `σ.Regions`
    have a valuation the layout reads off it. Then every decoding of the function bytes of
    `body` is constant time under `ctRegime`, with no side condition on the steps, between
    entry states that satisfy `σ.Regions` and agree on the public data of `σ`. -/
theorem v1Loop_bytes_ct (Pj : JLeakParams) (σ : AbiLayout) (a : AbiNames) (fuse : Bool)
    (body : Lcmd) {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (h : v1LoopB σ a fuse body c = true) (hlk : v1LoopLB σ fuse body c = true)
    (L : Labels Γ) (hct : ConstantTime (PubEqV L) (ComL.ctLeak (jLeakModel Pj) c))
    (hL : PubLabelsOK σ L)
    (hval : ∀ sa, σ.Regions sa → ∃ V : Ctxt.Valuation Γ, AbiValOf σ sa V)
    {prog : List RInstr} (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂)
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') := by
  unfold v1LoopB at h
  unfold v1LoopLB at hlk
  split at h
  · rename_i m _ update count init invs
    rw [Bool.and_eq_true] at h
    obtain ⟨hg0, hn⟩ := h
    simp only [Bool.and_eq_true] at hg0
    obtain ⟨⟨hamem, hexpB⟩, hl⟩ := hg0
    have hupd := arrMemNB_sound update hamem
    have hexp := comExpOKB_sound update hexpB
    have hcert := loopCertB_of_loopCertNB hl a.outArg a.inArgs a.abiArgs
    split at hn
    · rename_i out cR hout hcnt
      simp only [Bool.and_eq_true] at hn
      obtain ⟨-, hroute⟩ := hn
      simp only [hout, hcnt] at hlk
      set seeds := certSeeds (Γ := Γ) update out cR with hseeds
      set loop := guardedFlagLoopLinstrRM Γ.length (Γ.length + 0x40000000)
        (certRen (Γ := Γ) update out (loopCtr Γ.length)) (certBody update invs out) with hloop
      set ps := synthRen (argBind σ exportReg ++ seeds ++ loop)
        (virtImg (slotArrOf σ exportReg) body) (argBind σ exportReg ++ seeds).length with hps
      have hnode : seeds ++ loop = X86Backend.ExportCertLoop.certNode update invs out cR :=
        (certNode_eq update invs out cR).symm
      have hqs : ∀ i ∈ seeds, ∀ r, JasminLsemMemFLeak.instrLeakB r i = [] :=
        loopSeedsRM_quiet _ _ _ _ _
      have hroute' := hroute
      simp only [routeB, Bool.and_eq_true] at hroute'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, -⟩, -⟩, -⟩, -⟩, hfr⟩, hent⟩, hren⟩, -⟩, -⟩ := hroute'
      have R := renB_spec hren
      have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) → unren ps (renOf ps A) = A := by
        intro q A n h
        obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
        exact (R.unr j (List.getElem?_eq_some_iff.mp hj).1).2
      rintro sa₁ sa₂ u₁ u₂ ⟨hag, hreg₁, hreg₂⟩ hb₁ hb₂
      have E₁ := entryB_spec hent sa₁
      have E₂ := entryB_spec hent sa₂
      have hrsp : frameRsp body sa₂ = frameRsp body sa₁ := by
        unfold frameRsp
        rw [hag.1]
      have hfrE : frameE body sa₂ = frameE body sa₁ := by
        unfold frameE
        rw [hrsp]
      have hsep := imgSep_slotRen (ren := renOf ps)
        (imgSep_of_regions E₁.rs hreg₁ hfr E₁.len E₁.slot
          X86Backend.ImageAddrRoute.slotArrOf_not_fa) hun
      have hCT := route_bytes_ct_loop Pj update count init invs a.outArg a.inArgs a.abiArgs
        hupd hexp hcert out cR hout hcnt hroute hnode hqs L "" hct hlk hsep
        (fun _ _ => True) hdec
      obtain ⟨V₁, hV₁⟩ := hval sa₁ hreg₁
      obtain ⟨V₂, hV₂⟩ := hval sa₂ hreg₂
      have hk₁ := virtB_checked_run update count init invs a.outArg a.inArgs a.abiArgs hupd
        hexp hcert out cR hout hcnt hroute hnode hqs sa₁ hreg₁ V₁ hV₁ ""
      have hk₂ := virtB_checked_run update count init invs a.outArg a.inArgs a.abiArgs hupd
        hexp hcert out cR hout hcnt hroute hnode hqs sa₂ hreg₂ V₂ hV₂ ""
      have himg : ∀ sa, (∃ f t, lsemFuelMemFk true
            (singletonProgM "" (virtB σ exportReg seeds loop ps fuse)) f
            (routeEntry σ body ps "" sa) = some t) →
          ∃ f t, lsemFuelMemFk true (singletonProgM ""
            (virtImg (slotRen (slotArrOf σ exportReg) (renOf ps)) body)) f
            (routeEntry σ body ps "" sa) = some t := by
        rintro sa ⟨f, t, hk⟩
        obtain ⟨f', t', hr', -⟩ := ownedCheckMC_sound hck "" _ t rfl rfl f hk
        exact ⟨f', t', hr'⟩
      have hentA : ∀ sa : AState, Entry sa (entryA σ sa) := fun sa =>
        ⟨rfl, fun R hR => by
          have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
            simp only [entryA, hR, ite_true]
          unfold JasminLsemWidthN.LstateN.getW
          rw [hl]
          simp, rfl⟩
      have hrel₁ := imgRel_entryV (σ := σ) (nm := exportReg) (fr := frameE body sa₁)
        (sa := sa₁) (body := body) (fn := "") (ren := renOf ps) (un := unren ps)
        (E₁.argSrc hreg₁.stackIn) (fun _ _ hs => entryB_save hent hs)
        (fun j hj => (R.unr j hj).2)
      have hrel₂ := imgRel_entryV (σ := σ) (nm := exportReg) (fr := frameE body sa₂)
        (sa := sa₂) (body := body) (fn := "") (ren := renOf ps) (un := unren ps)
        (E₂.argSrc hreg₂.stackIn) (fun _ _ hs => entryB_save hent hs)
        (fun j hj => (R.unr j hj).2)
      have hbase : ∀ q A n, slotRen (slotArrOf σ exportReg) (renOf ps) q = some (A, n) →
          abiBase (abiReg σ) sa₂ (unren ps A) = abiBase (abiReg σ) sa₁ (unren ps A) := by
        intro q A n hq
        obtain ⟨A0, hA0, rfl⟩ := slotRen_some hq
        obtain ⟨j, a0, hj, hkind, rfl, -⟩ := slotArrOf_some hA0
        rw [(R.unr j (List.getElem?_eq_some_iff.mp hj).1).2, abiBase_argName hj,
          abiBase_argName hj]
        exact (hag.2 a0 (List.mem_of_getElem? hj) (by simp [AbiLayout.argPub, hkind])).symm
      have hrel₂' := imgRel_congr_base hbase hrel₂
      refine hCT sa₁ sa₂ u₁ u₂ ⟨rfl, hrsp, (entryA σ sa₁, false), (entryA σ sa₂, false),
        ⟨routeEntry σ body ps "" sa₁, routeEntry σ body ps "" sa₂, ?_, rfl, rfl, rfl, hrel₁,
          ?_, himg sa₁ hk₁, himg sa₂ hk₂⟩, hentA sa₁, hentA sa₂⟩ hb₁ hb₂
      · exact ⟨⟨sa₁, sa₂, V₁, V₂, hV₁, hV₂, pubEqV_of_pubAgree hL hag hV₁ hV₂,
          hreg₁.stackIn, hreg₂.stackIn, rfl, rfl⟩, rfl, rfl, rfl, rfl, hk₁, hk₂⟩
      · have key : ∀ fr : String → Option (BitVec 64), fr = frameE body sa₁ →
            ImgRel fr (slotRen (slotArrOf σ exportReg) (renOf ps))
              (fun A => abiBase (abiReg σ) sa₁ (unren ps A)) body
              (routeEntry σ body ps "" sa₂) (entryA σ sa₂) false →
            ImgRel (frameE body sa₁) (slotRen (slotArrOf σ exportReg) (renOf ps))
              (fun A => abiBase (abiReg σ) sa₁ (unren ps A)) body
              (routeEntry σ body ps "" sa₂) (entryA σ sa₂) false := by
          rintro _ rfl h
          exact h
        exact key _ hfrE hrel₂'
    · cases hn
  · cases h

/-! ## 7. The compiler -/

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryVals_of_typed)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto
open _root_.Hax (TExpr Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (hax64WExit)
open scoped ENNReal

/-- **The check of the secrecy record against the layout**: every parameter the record `s`
    lists as public is public under `σ`, and is a scalar parameter or an array parameter
    whose register is in `σ.pubWords`. -/
def pubLabelsB (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) : Bool :=
  σ.args.all fun a =>
    match paramLevel s a.name with
    | .Public => (a.kind == .scalar || σ.pubWords.contains a.reg) && σ.argPub a
    | _ => true

/-- A variable of the mapped context of the parameters `as` that the labels of the record
    `s` mark public is a register variable of a parameter public under `σ`, or an array
    variable of a public array of `σ`, when every parameter of `as` passes the check of
    `pubLabelsB`. -/
theorem pubLabels_lookup (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) :
    ∀ (as : List AbiArg),
      (∀ a ∈ as, paramLevel s a.name = .Public →
        (a.kind = .scalar ∨ a.reg ∈ σ.pubWords) ∧ σ.argPub a = true) →
      ∀ {t : JasminTy} (v : Ctxt.Var (d := jasminDialect)
        (mapCtx ((entryCtx (as.map fun a => (a.name, abiKindArr a.kind))).map catTy)) t),
      lvlOf v (mapLabels (nfLabels s (as.map fun a => (a.name, abiKindArr a.kind)))) = .Public →
      (∃ w a, t = .reg w ∧ as[JasminLprogExport.varIndex v]? = some a ∧ σ.argPub a = true) ∨
        ∃ n a, t = .stackArr 64 n ∧ as[JasminLprogExport.varIndex v]? = some a ∧
          a.kind = .words n ∧ a.reg ∈ σ.pubWords
  | [], _, _, v, _ => nomatch v
  | a :: as, h, t, v, hv => by
      have ha := h a List.mem_cons_self
      obtain ⟨name, reg, kind⟩ := a
      cases v with
      | here =>
          obtain ⟨hk, hp⟩ := ha hv
          cases kind with
          | scalar => exact Or.inl ⟨64, _, rfl, rfl, hp⟩
          | words n =>
              have hm : reg ∈ σ.pubWords := hk.resolve_left (by simp)
              exact Or.inr ⟨n, _, rfl, rfl, rfl, hm⟩
      | there v =>
          rcases pubLabels_lookup s σ as
            (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) v hv with
            ⟨w, b, hw, hb, hp⟩ | ⟨n, b, hn, hb, hk, hm⟩
          · exact Or.inl ⟨w, b, hw, hb, hp⟩
          · exact Or.inr ⟨n, b, hn, hb, hk, hm⟩

/-- **The labels of a secrecy record agree with the public data of the layout** when the
    check `pubLabelsB` accepts. -/
theorem pubLabelsOK_of_pubLabelsB {s : _root_.Hax.FnSecrecy} {σ : AbiLayout}
    (h : pubLabelsB s σ = true) : PubLabelsOK σ (mapLabels (nfLabels s (abiEntry σ))) := by
  have hrev : abiEntry σ = σ.args.reverse.map fun a => (a.name, abiKindArr a.kind) := by
    simp [abiEntry, abiParamsArr, List.map_reverse]
  have hall : ∀ a ∈ σ.args.reverse, paramLevel s a.name = .Public →
      (a.kind = .scalar ∨ a.reg ∈ σ.pubWords) ∧ σ.argPub a = true := by
    intro a ha hp
    have := List.all_eq_true.mp h a (List.mem_reverse.mp ha)
    rw [hp] at this
    simpa using this
  show ∀ (t : JasminTy) (v : Ctxt.Var (d := jasminDialect)
      (mapCtx ((entryCtx (abiEntry σ)).map catTy)) t),
      lvlOf v (mapLabels (nfLabels s (abiEntry σ))) = .Public →
      (∃ w a, t = .reg w ∧ σ.args[argIdx v]? = some a ∧ σ.argPub a = true) ∨
        ∃ n a, t = .stackArr 64 n ∧ σ.args[argIdx v]? = some a ∧ a.kind = .words n ∧
          a.reg ∈ σ.pubWords
  rw [hrev]
  intro t v hv
  have hlt := JasminLsemSimulation.varIndex_lt v
  simp only [mapCtx, entryCtx, List.length_map, List.length_reverse] at hlt
  have hidx : ∀ a, σ.args.reverse[JasminLprogExport.varIndex v]? = some a →
      σ.args[argIdx v]? = some a := by
    intro a ha
    simp only [X86Backend.ExportCertEntry.argIdx, mapCtx, entryCtx, List.length_map,
      List.length_reverse]
    exact (List.getElem?_reverse hlt).symm.trans ha
  rcases pubLabels_lookup s σ σ.args.reverse hall v hv with
    ⟨w, a, hw, ha, hp⟩ | ⟨n, a, hn, ha, hk, hm⟩
  · exact Or.inl ⟨w, a, hw, hidx a ha, hp⟩
  · exact Or.inr ⟨n, a, hn, hidx a ha, hk, hm⟩

/-- Every entry state has a valuation of the context of the route program that the layout
    reads off it, when the names of the layout are pairwise distinct. -/
theorem exists_abiValOf (σ : AbiLayout) (hnd : σ.envNames.Nodup) (sa : AState) :
    ∃ V : Ctxt.Valuation (nfCtx σ), AbiValOf σ sa V := by
  have hσ := σ.envOf_canonEnv hnd sa
  obtain ⟨V, hV⟩ := entryVals_of_typed (ps := abiEntry σ)
    (fun x t hm => entryTyped_of_envOf_arr hσ x t (List.mem_reverse.mp hm))
  exact ⟨ctMapValD (mapVal V), abiValOf_mapVal hσ V hV⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
