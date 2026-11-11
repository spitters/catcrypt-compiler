/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefRutt

/-!
# The arguments of an image call from the call of the reference

At a call of the reference of a calling body that the simulation of the segment check matches
to a call of its image, the call state of the reference and the image state agree on the operands
of the call (the names `segOutsAt` of the exit), the segment check gives the image call the same
shadow instruction, whose operands are the site arguments, and the dead table of the image keeps
the site arguments alive, so that `ImgRelF` and `ACorr` carry their words to the registers at the
entry of the callee (`ImageAddrCall.args_entry`). For a word event the argument words are those of
the operands.

## Main results

* `siteMapL_shadow`: the site map of two lists of sites with equal shadow instructions sends a
  site to a site with the same shadow instruction.
* `siteArgs_entry`: at an image call matched to a call of the reference, the callee-entry
  registers of the site arguments hold the argument words of the call of the reference.
* `callSym_eq`: the symbol of an image call matched to a call of the reference is the symbol of
  the call.
* `eventArgs_entry`: the argument words of a word event at a call site of the reference are the
  callee-entry registers of the site arguments of the matched image call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefArgs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (shadowAt siteMap siteMapL
  segOutsAt calleeSegB regsOf regsOf_map_reg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (argWord argWord_congr entryOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (goto)

/-- **The site map of two lists of sites with equal shadow instructions** sends a site to a site
    with the same shadow instruction. -/
theorem siteMapL_shadow {B B' : List LinstrRM} :
    ∀ {ps qs : List Nat}, ps.map (shadowAt B) = qs.map (shadowAt B') →
      ∀ {x q : Nat}, siteMapL ps qs x = some q → shadowAt B' q = shadowAt B x
  | [], _, _, _, _, h => by simp [siteMapL] at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | p :: ps, q' :: qs, h, x, q, hq => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [siteMapL] at hq
      split at hq
      · rename_i hx
        obtain rfl := Option.some.inj hq
        rw [hx, h.1]
      · exact siteMapL_shadow h.2 hq


/-- **The arguments of an image call from the call of the reference.** Let the segment check
    `calleeSegB` accept the reference `ref` and the image `callImg sl site b` of a printed body
    `b` that passes `callSitesB`, and let the dead table `E` keep the site arguments of every call
    alive (`callDeadSymB`). At the shadow instruction of a call at `p` in
    `ref`, from a state `u` and an image state `u'` agreeing on the names `segOutsAt` of the exit
    at `p`, at the site `q` that the site map gives, whose arguments are general-purpose names,
    and at a state `sA` of the address machine that `ACorr` relates to a state `sa₁` that
    `ImgRelF` relates to `u'` at `q`: the operands of the call are the registers of the site
    arguments, and the registers of the site arguments at the entry of the callee from `sA`
    hold their words in `u`. -/
theorem siteArgs_entry {PT : LprogIsa.ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref : List LinstrRM}
    {sl : String → Option (String × Nat)} {site : Nat → String × List String} {b : Lcmd}
    (hseg : calleeSegB PT fn fin ins outs ref (X86Backend.ImageAddrCall.callImg sl site b) = true)
    (hcs : X86Backend.ImageAddrCall.callSitesB sl b = true)
    {sig : String → X86Backend.Callee.CalleeSig} {out : String → Bool} {E : Nat → List String}
    (hdead : X86Backend.ImageAddrCall.callDeadSymB sig out site E b = true)
    {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : X86Backend.ImageAddrSim.ImgSep frame slotArr base rsp)
    {p : Nat} {dst f : String} {srcs : List LOperand} {tag : MemTag}
    (hp : ref[p]? = some (LprogIsa.callShadow dst f srcs, tag))
    {u u' : LstateMF} (hO : Obs (segOutsAt ref ins outs (some p)) u u')
    {q : Nat} (hq : siteMap PT ref (X86Backend.ImageAddrCall.callImg sl site b) (some p) = some q)
    (hgp : ∀ a ∈ (site q).2, gpOk a = true)
    {sa₁ : JasminLsemAddrMem.LstateA} {sA : Ascent.AddrMem.AState}
    (hrel : X86Backend.ImageAddrCall.ImgRelF frame slotArr base b (E q) (goto u' q) sa₁)
    (hc : X86Backend.DecodePrintedAddr.ACorr rsp sA sa₁) (ret : Nat) :
    srcs = (site q).2.map LOperand.reg
      ∧ (site q).2.map (fun a => (entryOf ret sA).regs (phys a))
        = (site q).2.map (argWord u.prog.base.reg) := by
  simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq] at hseg
  obtain ⟨⟨hmap, -⟩, -⟩ := hseg
  have hsh : shadowAt ref p = some (dst, f, srcs) := by
    simp only [shadowAt, hp, Option.bind_some, LprogIsa.shadowCall?_callShadow]
  have himg := siteMapL_shadow hmap hq
  rw [hsh] at himg
  -- The image instruction at `q` is the shadow instruction of the call of the body at `q`.
  obtain ⟨i, hi, hsi⟩ : ∃ i, (X86Backend.ImageAddrCall.callImg sl site b)[q]? = some i
      ∧ LprogIsa.shadowCall? i.fst = some (dst, f, srcs) := by
    unfold shadowAt at himg
    cases hr : (X86Backend.ImageAddrCall.callImg sl site b)[q]? with
    | none => simp [hr] at himg
    | some i =>
        simp only [hr, Option.bind_some] at himg
        exact ⟨i, rfl, himg⟩
  obtain ⟨⟨bi, ra, l, hb, hbi⟩, hx⟩ := RegionLinkCompose.shadowCall?_callImg site hcs hi hsi
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hsrcs⟩ := hx
  refine ⟨hsrcs, ?_⟩
  -- The site arguments are alive at `q`, and agree between `u` and `u'`.
  have halive := (X86Backend.ImageAddrCall.callDeadSymB_spec hdead hb hbi).1
  obtain ⟨s', zf, hag, hR⟩ := hrel
  rw [X86Backend.ImageAddrCall.args_entry hsep hgp hR hc ret]
  refine List.map_congr_left fun a ha => ?_
  have hmem : a ∈ segOutsAt ref ins outs (some p) := by
    simp only [segOutsAt, hsh]
    rw [hsrcs, regsOf_map_reg]
    exact List.mem_append_left _ ha
  refine argWord_congr ?_
  rw [← hag.regs a (halive a ha)]
  exact hO.1 a hmem


/-- **The argument words of an event at an image call are the callee-entry registers of the site
    arguments.** In the setting of `siteArgs_entry`, at a call site of a word event `ev` at `u`
    in `ref`, whose argument types have no array position, the argument words of `ev` are the
    registers of the site arguments at the entry of the callee from `sA`. -/
theorem eventArgs_entry {PT : LprogIsa.ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref : List LinstrRM}
    {sl : String → Option (String × Nat)} {site : Nat → String × List String} {b : Lcmd}
    (hseg : calleeSegB PT fn fin ins outs ref (X86Backend.ImageAddrCall.callImg sl site b) = true)
    (hcs : X86Backend.ImageAddrCall.callSitesB sl b = true)
    {sig : String → X86Backend.Callee.CalleeSig} {out : String → Bool} {E : Nat → List String}
    (hdead : X86Backend.ImageAddrCall.callDeadSymB sig out site E b = true)
    {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : X86Backend.ImageAddrSim.ImgSep frame slotArr base rsp) {fn' : String}
    {ev : NFProgCallTree.NFCall JasminDialect.jasminDialect} {u : LstateMF} {p : Nat}
    (hsi : NFProgCallTreeExport.CallSite (singletonProgM fn' ref) ev u)
    (hat : Ascent.IsaCfg.atPc (singletonProgM fn' ref) p u)
    (hw : ExportRegions.arrArgsOf ev.argTys = fun _ => none)
    {u' : LstateMF} (hO : Obs (segOutsAt ref ins outs (some p)) u u')
    {q : Nat} (hq : siteMap PT ref (X86Backend.ImageAddrCall.callImg sl site b) (some p) = some q)
    (hgp : ∀ a ∈ (site q).2, gpOk a = true)
    {sa₁ : JasminLsemAddrMem.LstateA} {sA : Ascent.AddrMem.AState}
    (hrel : X86Backend.ImageAddrCall.ImgRelF frame slotArr base b (E q) (goto u' q) sa₁)
    (hc : X86Backend.DecodePrintedAddr.ACorr rsp sA sa₁) (ret : Nat) :
    ExportRegions.wordsOf ev.args = (site q).2.map (fun a => (entryOf ret sA).regs (phys a)) := by
  obtain ⟨dst, srcs, tag, k, hat', hf, -, hrd⟩ := hsi
  obtain rfl : k = p := hat'.2.symm.trans hat.2
  obtain ⟨hsrcs, hent⟩ := siteArgs_entry hseg hcs hdead hsep hf hO hq hgp hrel hc ret
  rw [hent]
  rw [hw, LprogIsa.argsRead_none, hsrcs] at hrd
  exact X86Backend.ImageAddrCall.mapM_reg_argWord _ _ _ hrd


/-- **The symbol of an image call matched to a call of the reference is the symbol of the call.**
    -/
theorem callSym_eq {PT : LprogIsa.ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref : List LinstrRM}
    {sl : String → Option (String × Nat)} {site : Nat → String × List String} {b : Lcmd}
    (hseg : calleeSegB PT fn fin ins outs ref (X86Backend.ImageAddrCall.callImg sl site b) = true)
    (hcs : X86Backend.ImageAddrCall.callSitesB sl b = true)
    {p : Nat} {dst g : String} {srcs : List LOperand} {tag : MemTag}
    (hp : ref[p]? = some (LprogIsa.callShadow dst g srcs, tag))
    {q : Nat} (hq : siteMap PT ref (X86Backend.ImageAddrCall.callImg sl site b) (some p) = some q)
    {bi : Linstr} {ra : Option String} {f : String} {l : LLabel} (hb : b[q]? = some bi)
    (hbi : bi.li_i = .Lcall ra (f, l)) : f = g := by
  simp only [calleeSegB, Bool.and_eq_true, beq_iff_eq] at hseg
  obtain ⟨⟨hmap, -⟩, -⟩ := hseg
  have hsh : shadowAt ref p = some (dst, g, srcs) := by
    simp only [shadowAt, hp, Option.bind_some, LprogIsa.shadowCall?_callShadow]
  have himg := siteMapL_shadow hmap hq
  rw [hsh] at himg
  obtain ⟨i, hi, hsi⟩ : ∃ i, (X86Backend.ImageAddrCall.callImg sl site b)[q]? = some i
      ∧ LprogIsa.shadowCall? i.fst = some (dst, g, srcs) := by
    unfold shadowAt at himg
    cases hr : (X86Backend.ImageAddrCall.callImg sl site b)[q]? with
    | none => simp [hr] at himg
    | some i =>
        simp only [hr, Option.bind_some] at himg
        exact ⟨i, rfl, himg⟩
  obtain ⟨⟨bi', ra', l', hb', hbi'⟩, -⟩ := RegionLinkCompose.shadowCall?_callImg site hcs hi hsi
  rw [hb] at hb'
  obtain rfl := Option.some.inj hb'
  rw [hbi] at hbi'
  simp only [LinstrR.Lcall.injEq, Prod.mk.injEq] at hbi'
  exact hbi'.2.1

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefArgs
